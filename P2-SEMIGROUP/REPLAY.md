# How to replay the Project 2 Lean checks

Anyone can rebuild these packages and compare the results. This is a reproduction of a build, not a review of the mathematics.

## 1. Install the pinned toolchain manager

    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/3cc76985a1becb3c03cd65c1c5007e6f186ae474/elan-init.sh -o elan-init.sh
    echo "a620ff1641616222c8d37c54845492004bb84d6877cdbc944dd65c1aa685bf53  elan-init.sh" | sha256sum -c -
    sh elan-init.sh -y --default-toolchain none

Then clone this repository and enter P2-SEMIGROUP.

## 2. Core package (no Mathlib)

    cd p2-core
    sha256sum -c SOURCE.SHA256SUMS
    lake build 2>&1 | tee build.log
    grep -cE 'depends on axioms|does not depend on any axioms' build.log
    grep -c sorryAx build.log
    for f in controls/NegativeControl.lean controls/NegativeControl2.lean; do
      lake env lean "$f" > /dev/null 2>&1 && echo "UNEXPECTED_PASS $f" || echo "REJECTED $f"
    done

Expected: all checksums OK, 27 axiom reports, 0 occurrences of sorryAx, both controls REJECTED. Every axiom list should contain only propext and Quot.sound. The declared toolchain is Lean v4.35.0-rc4. CI also builds this package under v4.36.0:

    elan override set leanprover/lean4:v4.36.0
    lake build

## 3. Mathlib package (rank transfer lemma)

    cd ../p2-mathlib
    lake exe cache get
    lake build 2>&1 | tee build.log
    grep -cE 'depends on axioms|does not depend on any axioms' build.log

Expected: 2 axiom reports, no sorryAx, no "declaration uses" warning. Allowed axioms: propext, Classical.choice, Quot.sound. The dependency set is pinned in lake-manifest.json.

## 4. Bridge package (cone, closure and translation theorems)

    cd ../p2-bridge
    lake exe cache get
    lake build 2>&1 | tee build.log
    grep -cE 'depends on axioms|does not depend on any axioms' build.log

Expected: 33 axiom reports (24 from the imported core kernels and 9 from the bridge), no sorryAx, no "declaration uses" warning. Allowed axioms: propext, Classical.choice, Quot.sound.

## What a match means

A match shows that these source files compile with the stated toolchain and dependency commits, and that the reported axiom dependencies agree. It does not show that the formalized statements capture the intended mathematics, that the draft is correct, or that anything outside REPORT.md is formalized. The overall theorem status remains DRAFT_REQUIRING_REVIEW.

## Reporting a replay

Open an issue on the AQARION repository with: the commit you built, your platform, the three counts from steps 2 to 4, and any difference from the expected values.
