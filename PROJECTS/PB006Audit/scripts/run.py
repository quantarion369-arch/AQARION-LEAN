#!/usr/bin/env python3
import hashlib
import json
import os
import platform
import re
import statistics
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / "logs"
LOGS.mkdir(exist_ok=True)
os.chdir(ROOT)

TIMEOUT = int(os.environ.get("AQ_TIMEOUT", "300"))
results = {}
log_number = 0

def run(label, command, timeout=TIMEOUT):
    global log_number
    log_number += 1
    start = time.perf_counter()
    try:
        p = subprocess.run(
            command, cwd=ROOT, text=True,
            capture_output=True, timeout=timeout
        )
        record = {
            "command": command,
            "returncode": p.returncode,
            "seconds": time.perf_counter() - start,
            "stdout": p.stdout,
            "stderr": p.stderr,
            "timeout": False,
        }
    except subprocess.TimeoutExpired as e:
        def text(value):
            if isinstance(value, bytes):
                return value.decode(errors="replace")
            return value or ""
        record = {
            "command": command,
            "returncode": None,
            "seconds": time.perf_counter() - start,
            "stdout": text(e.stdout),
            "stderr": text(e.stderr),
            "timeout": True,
        }
    filename = "%03d-%s.json" % (log_number, label)
    (LOGS / filename).write_text(
        json.dumps(record, indent=2), encoding="utf-8"
    )
    return record

def output(record):
    return record["stdout"] + chr(10) + record["stderr"]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def save_receipt():
    paths = [
        ROOT / "lean-toolchain",
        ROOT / "lakefile.lean",
        ROOT / "PB006Audit.lean",
        ROOT / "Main.lean",
        ROOT / "scripts/run.py",
    ] + sorted((ROOT / "PB006Audit").glob("*.lean"))
    receipt = {
        "suite": "PB006Audit",
        "platform": platform.platform(),
        "python": platform.python_version(),
        "source_hashes": {
            str(p.relative_to(ROOT)): sha(p) for p in paths
        },
        "results": results,
        "promotion": "BLOCKED",
        "general_counting_theorem": "NOT_FORMALIZED",
    }
    path = LOGS / "receipt.json"
    path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    print("Receipt SHA-256:", sha(path))

results["lean_version"] = run("lean-version", ["lake", "env", "lean", "--version"])
results["lake_version"] = run("lake-version", ["lake", "--version"])

build = run("build", ["lake", "build"])
results["build"] = build

if build["returncode"] != 0:
    print(output(build))
    print("BUILD FAILED: later checks not run.")
    save_receipt()
    sys.exit(1)

# Per-theorem axiom audit.
names = [
    ("empty_decide", "kernel"),
    ("singleton_decide", "kernel"),
]
for stem in ["a112", "a22", "a222", "a24", "a33"]:
    names.append((stem + "_decide", "kernel"))
    names.append((stem + "_native", "native"))

standard = {"propext", "Quot.sound", "Classical.choice"}
native_known = {"Lean.ofReduceBool", "Lean.trustCompiler"}
audits = []

for name, lane in names:
    path = LOGS / ("Audit_" + name + ".lean")
    path.write_text(
        "import PB006Audit.Anchors\n"
        "#print axioms PB006Audit.%s\n" % name,
        encoding="utf-8"
    )
    record = run(
        "audit-" + name, ["lake", "env", "lean", str(path)]
    )
    text = output(record)
    match = re.search("depends on axioms:" + chr(92) + "s*" + chr(92) + "[" + "([^]]*)" + chr(92) + "]", text)
    if match:
        axioms = [
            a.strip() for a in match.group(1).split(",") if a.strip()
        ]
        parsed = True
    elif "does not depend on any axioms" in text:
        axioms = []
        parsed = True
    else:
        axioms = []
        parsed = False

    allowed = standard if lane == "kernel" else standard | native_known
    unexpected = sorted(set(axioms) - allowed)
    passed = (
        record["returncode"] == 0
        and parsed
        and "sorryAx" not in axioms
        and not unexpected
    )
    audits.append({
        "theorem": name,
        "lane": lane,
        "axioms": axioms,
        "unexpected": unexpected,
        "passed": passed,
        "note": (
            "Native lane is not kernel-only certification."
            if lane == "native" else "Kernel-reduction anchor."
        ),
    })

results["axiom_audits"] = audits

# Fail closed on explicit admissions/custom axioms in saved source.
source_text = chr(10).join(
    p.read_text(encoding="utf-8")
    for p in (ROOT / "PB006Audit").glob("*.lean")
)
results["source_screen"] = {
    "forbidden_token_present": bool(
        re.search(chr(92) + "b(sorry|admit|axiom)" + chr(92) + "b", source_text)
    )
}

# Benchmarks: end-to-end elapsed times, not instruction-level comparisons.
bench_build = run("bench-build", ["lake", "build", "pb006bench"])
results["benchmark_build"] = bench_build

benchmarks = []
for count, expected in [(3, 31), (4, 164), (5, 999), (6, 6841)]:
    for lane in ["decide", "native_decide", "eval"]:
        path = LOGS / ("Bench_%s_%d.lean" % (lane, count))
        if lane == "eval":
            body = "#eval PB006Audit.weightedBell (List.replicate %d 2)\n" % count
        else:
            body = (
                "set_option maxRecDepth 100000\n"
                "set_option maxHeartbeats 10000000\n"
                "example : PB006Audit.weightedBell "
                "(List.replicate %d 2) = %d := by %s\n"
            ) % (count, expected, lane)
        path.write_text(
            "import PB006Audit.Basic\n" + body, encoding="utf-8"
        )
        samples = [
            run(
                "bench-%s-%d-%d" % (lane, count, i),
                ["lake", "env", "lean", str(path)]
            )
            for i in range(3)
        ]
        passed = all(s["returncode"] == 0 for s in samples)
        if lane == "eval":
            passed = passed and all(
                str(expected) in s["stdout"].split() for s in samples
            )
        benchmarks.append({
            "lane": lane, "cycles": count,
            "expected": expected,
            "median_seconds": statistics.median(
                s["seconds"] for s in samples
            ),
            "passed": passed,
        })

    if bench_build["returncode"] == 0:
        binary = ROOT / ".lake/build/bin/pb006bench"
        samples = [
            run(
                "bench-binary-%d-%d" % (count, i),
                [str(binary), str(count)]
            )
            for i in range(3)
        ]
        benchmarks.append({
            "lane": "compiled_executable",
            "cycles": count,
            "expected": expected,
            "median_seconds": statistics.median(
                s["seconds"] for s in samples
            ),
            "passed": all(
                s["returncode"] == 0
                and s["stdout"].strip() == str(expected)
                for s in samples
            ),
        })

results["benchmarks"] = benchmarks

# Isolated formula mutations, preserving the baseline files.
original = (ROOT / "PB006Audit/Basic.lean").read_text(encoding="utf-8")

def transform_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError("Mutation target not unique: " + old)
    return text.replace(old, new, 1)

mutation_specs = [
    {
        "name": "exponent",
        "old": "d ^ (block.length - 1)",
        "new": "d ^ block.length",
        "anchors": [("a112", "[1,1,2]", 7), ("a24", "[2,4]", 9)],
    },
    {
        "name": "gcd_to_lcm",
        "old": "xs.foldl Nat.gcd x",
        "new": "xs.foldl Nat.lcm x",
        "anchors": [("a112", "[1,1,2]", 7), ("a24", "[2,4]", 9)],
    },
    {
        "name": "drop_singleton_component",
        "old": "([x] :: part) :: insertIntoBlocks x part",
        "new": "insertIntoBlocks x part",
        "anchors": [("a24", "[2,4]", 9)],
    },
]

mutations = []
for spec in mutation_specs:
    changed = transform_once(original, spec["old"], spec["new"])
    changed = changed.replace(
        "namespace PB006Audit", "namespace Mutant", 1
    ).replace("end PB006Audit", "end Mutant", 1)
    for name, cycles, expected in spec["anchors"]:
        path = LOGS / ("Mut_%s_%s.lean" % (spec["name"], name))
        path.write_text(
            changed
            + "\nexample : Mutant.weightedBell %s = %d := by native_decide\n"
              % (cycles, expected),
            encoding="utf-8"
        )
        record = run(
            "mutation-%s-%s" % (spec["name"], name),
            ["lake", "env", "lean", str(path)]
        )
        text = output(record).lower()
        detected = (
            record["returncode"] not in (0, None)
            and "evaluated" in text
            and "false" in text
        )
        mutations.append({
            "mutation": spec["name"],
            "anchor": name,
            "source_changed": changed != original,
            "detected_as_false": detected,
            "returncode": record["returncode"],
        })

results["mutations"] = mutations
results["mutation_summary"] = {
    "detected": sum(m["detected_as_false"] for m in mutations),
    "required": len(mutations),
}

checks = [
    all(a["passed"] for a in audits),
    not results["source_screen"]["forbidden_token_present"],
    bench_build["returncode"] == 0,
    all(b["passed"] for b in benchmarks),
    all(m["detected_as_false"] for m in mutations),
]
results["overall_pass"] = all(checks)

print("\nAXIOM AUDIT")
for a in audits:
    print(a["theorem"], a["lane"], a["axioms"],
          "PASS" if a["passed"] else "BLOCK")

print("\nBENCHMARKS: median end-to-end seconds")
for b in benchmarks:
    print(b["lane"], b["cycles"],
          "%.6f" % b["median_seconds"],
          "PASS" if b["passed"] else "FAIL/TIMEOUT")

print("\nMUTATIONS")
for m in mutations:
    print(m["mutation"], m["anchor"],
          "DETECTED" if m["detected_as_false"] else "BLOCK")

print("\nOVERALL:", "PASS" if results["overall_pass"] else "BLOCK")
print("General counting theorem: NOT FORMALIZED")
print("Promotion: BLOCKED")
save_receipt()
sys.exit(0 if results["overall_pass"] else 1)
