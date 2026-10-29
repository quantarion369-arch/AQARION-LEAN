from fractions import Fraction as Q
from itertools import combinations
from math import prod
from pathlib import Path
import csv
import hashlib
import io
import json

BASE = Path(__file__).resolve().parent
h = list(map(int, "000000101101"))
n = len(h)
features = [
    [], [0], [1], [2], [3], [4], [5],
    [0, 1], [0, 2], [0, 3], [1, 2], [1, 3],
]

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def matrix(fs):
    return [
        [prod(h[(i + t) % n] for t in s) for s in fs]
        for i in range(n)
    ]

def rank(matrix):
    a = [list(map(Q, row)) for row in matrix]
    r = 0
    for c in range(len(a[0])):
        p = next((i for i in range(r, len(a)) if a[i][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        pivot = a[r][c]
        a[r] = [x / pivot for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c]:
                factor = a[i][c]
                a[i] = [x - factor*y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r

def inverse_det(matrix):
    size = len(matrix)
    a = [
        [Q(x) for x in row] + [Q(i == j) for j in range(size)]
        for i, row in enumerate(matrix)
    ]
    determinant = Q(1)
    for c in range(size):
        p = next((i for i in range(c, size) if a[i][c]), None)
        require(p is not None, "Singular evaluation matrix")
        if p != c:
            a[c], a[p] = a[p], a[c]
            determinant = -determinant
        pivot = a[c][c]
        determinant *= pivot
        a[c] = [x / pivot for x in a[c]]
        for i in range(size):
            if i != c:
                factor = a[i][c]
                a[i] = [x - factor*y for x, y in zip(a[i], a[c])]
    inverse = [row[size:] for row in a]
    require(
        all(x.denominator == 1 for row in inverse for x in row),
        "Inverse is not integral",
    )
    return determinant, [[int(x) for x in row] for row in inverse]

def multiply(a, b):
    return [
        [sum(x*y for x, y in zip(row, col)) for col in zip(*b)]
        for row in a
    ]

def csv_bytes(rows):
    stream = io.StringIO(newline="")
    csv.writer(stream).writerows(rows)
    return stream.getvalue().encode("utf-8")

B = matrix(features)
det, inverse = inverse_det(B)
identity = [[int(i == j) for j in range(n)] for i in range(n)]

require(det == -1, "Determinant mismatch")
require(multiply(B, inverse) == identity, "B times inverse failed")
require(multiply(inverse, B) == identity, "Inverse times B failed")

frontier = []
all_degrees = {}
for L in range(1, 7):
    ranks = [
        rank(matrix([
            s for k in range(d + 1)
            for s in combinations(range(L), k)
        ]))
        for d in range(L + 1)
    ]
    distinct = len({
        tuple(h[(i + t) % n] for t in range(L))
        for i in range(n)
    })
    require(ranks[-1] == distinct, "History-count bound mismatch")
    require(all(r == distinct for r in ranks[2:]),
            "Higher-degree rank mismatch")
    frontier.append([L, ranks[0], ranks[1], ranks[min(2, L)], distinct])
    all_degrees[str(L)] = ranks

require(frontier == [
    [1, 1, 2, 2, 2], [2, 1, 3, 4, 4],
    [3, 1, 4, 7, 7], [4, 1, 5, 10, 10],
    [5, 1, 6, 11, 11], [6, 1, 7, 12, 12],
], "Frontier mismatch")

require(
    all(h[(i+t) % n] == 0 for i in (0, 1) for t in range(5)),
    "Five-observation collision mismatch",
)

linear = rank(matrix([[t] for t in range(n)]))
linear_constant = rank(matrix([[]] + [[t] for t in range(n)]))
quadratic = rank(matrix([
    s for k in range(3) for s in combinations(range(n), k)
]))
require((linear, linear_constant, quadratic) == (7, 7, 12),
        "All-time rank mismatch")

result = {
    "arithmetic": "exact fractions.Fraction; no floating point",
    "basis_determinant": int(det),
    "basis_rank": rank(B),
    "inverse_integral": True,
    "B_times_inverse_identity": True,
    "inverse_times_B_identity": True,
    "ranks_by_horizon_and_degree": all_degrees,
    "linear_rank_all_12_times": linear,
    "linear_plus_constant_rank_all_12_times": linear_constant,
    "quadratic_rank_all_12_times": quadratic,
    "minimum_consecutive_horizon": 6,
    "minimum_degree_at_horizon_6": 2,
    "lean_compilation_performed": False,
}

outputs = {
    "evaluation-matrix.csv": csv_bytes(B),
    "inverse-matrix.csv": csv_bytes(inverse),
    "horizon-degree-frontier.csv": csv_bytes([
        ["horizon", "degree_0", "degree_1", "degree_2",
         "maximum_any_degree"],
        *frontier,
    ]),
    "result.json": (json.dumps(result, indent=2) + "\n").encode(),
}

expected = {
    "evaluation-matrix.csv":
        "b6b9b72a1275bb1c2647344726c6d3808ada430f52e03eb89c0562e0d3327d95",
    "inverse-matrix.csv":
        "46d4dbc0314705d4cf2f544c9fc3f5f2dc3b290c6fbbc4ae8f7abf72aa906bff",
    "horizon-degree-frontier.csv":
        "66aabd76050707ad7e5b9210dd572c3a3be18b23e8f72d97c7a6db799929f26e",
    "result.json":
        "45acabb37fb9ee984795895e8185c97709432e7022db4a9ee96d14e977e2a275",
}

for name, data in outputs.items():
    actual = hashlib.sha256(data).hexdigest()
    require(actual == expected[name], "Output hash mismatch: " + name)

for name, data in outputs.items():
    (BASE / name).write_bytes(data)
    print("EXPECTED_HASH_MATCH=YES  " + name)

(BASE / "SHA256SUMS").write_text("".join(
    expected[name] + "  " + name + "\n" for name in outputs
))

print("BASIS_DETERMINANT=-1")
print("BASIS_RANK=12")
print("INVERSE_IDENTITIES=PASS")
print("HORIZON_FRONTIER=PASS")
print("ALL_TIME_RANKS=7,7,12")
print("LEAN_COMPILATION_PERFORMED=NO")
print("TWELVE_CYCLE_EXACT_REPLAY=PASS")
