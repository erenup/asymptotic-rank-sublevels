#!/usr/bin/env python3
"""Exact appended-minor ranks and tensor identities over Q(i)."""
import argparse
from fractions import Fraction
from itertools import combinations, permutations, product
import json
from pathlib import Path


def fail(message):
    raise SystemExit("FAIL: " + message)


def need(condition, message):
    if not condition:
        fail(message)


def exact_int(x):
    return type(x) is int


def no_duplicates(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, "duplicate JSON key")
        result[key] = value
    return result


def reject_number(value):
    fail("non-integer JSON number: " + value)


def tensor(entries, dims):
    need(type(entries) is list, "tensor entries must be a list")
    need(len(entries) <= 100, "tensor entry limit")
    ans = {}
    for item in entries:
        need(type(item) is list and len(item) == 2, "tensor entry shape")
        idx, value = item
        need(type(idx) is list and len(idx) == len(dims), "tensor index shape")
        need(all(exact_int(i) and 0 <= i < d for i, d in zip(idx, dims)),
             "tensor index range")
        need(exact_int(value) and 0 < abs(value) <= 100, "tensor coefficient")
        idx = tuple(idx)
        need(idx not in ans, "duplicate tensor coordinate")
        ans[idx] = value
    return ans


def rank(rows):
    """Sparse rational row elimination with no numerical tolerances."""
    basis = {}
    for raw in rows:
        row = {i: Fraction(x) for i, x in enumerate(raw) if x}
        while row:
            pivot = min(row)
            if pivot not in basis:
                divisor = row[pivot]
                basis[pivot] = {i: x / divisor for i, x in row.items()}
                break
            multiplier = row[pivot]
            for i, x in basis[pivot].items():
                new = row.get(i, Fraction(0)) - multiplier * x
                if new:
                    row[i] = new
                else:
                    row.pop(i, None)
    return len(basis)


def sign(p):
    return -1 if sum(p[i] > p[j] for i in range(len(p))
                     for j in range(i + 1, len(p))) % 2 else 1


def determinant3(matrix):
    return sum(sign(p) * matrix[0][p[0]] * matrix[1][p[1]] * matrix[2][p[2]]
               for p in permutations(range(3)))


def flatten(t, dims, left_modes):
    right_modes = [i for i in range(len(dims)) if i not in left_modes]
    left_indices = list(product(*(range(dims[i]) for i in left_modes)))
    right_indices = list(product(*(range(dims[i]) for i in right_modes)))
    rows = []
    for left in left_indices:
        row = []
        for right in right_indices:
            idx = [0] * len(dims)
            for i, x in zip(left_modes, left):
                idx[i] = x
            for i, x in zip(right_modes, right):
                idx[i] = x
            row.append(t.get(tuple(idx), 0))
        rows.append(row)
    return rows


def linearized_rows(t):
    """L(t) from all 4-row minors of [three T columns | one S column]."""
    coordinates = list(product(range(3), repeat=3))
    positions = {idx: i for i, idx in enumerate(coordinates)}
    equations = []
    for singleton in range(3):
        pair = [i for i in range(3) if i != singleton]
        pair_indices = list(product(range(3), repeat=2))

        def idx(pair_index, single):
            coordinate = [0, 0, 0]
            coordinate[singleton] = single
            for mode, value in zip(pair, pair_indices[pair_index]):
                coordinate[mode] = value
            return tuple(coordinate)

        matrix = [[t.get(idx(row, col), 0) for col in range(3)]
                  for row in range(9)]
        for appended_column in range(3):
            for selected in combinations(range(9), 4):
                equation = [0] * 27
                for position, row in enumerate(selected):
                    minor_rows = [matrix[r] for j, r in enumerate(selected)
                                  if j != position]
                    cofactor = (-1) ** (position + 3) * determinant3(minor_rows)
                    equation[positions[idx(row, appended_column)]] += cofactor
                equations.append(equation)
    return equations, coordinates


def cadd(x, y):
    return (x[0] + y[0], x[1] + y[1])


def cmul(x, y):
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def parse_basis(raw):
    need(type(raw) is list and len(raw) == 3, "basis matrix rows")
    ans = []
    for row in raw:
        need(type(row) is list and len(row) == 3, "basis matrix columns")
        new = []
        for z in row:
            need(type(z) is list and len(z) == 2
                 and all(exact_int(x) and abs(x) <= 10 for x in z),
                 "Gaussian integer basis entry")
            new.append(tuple(z))
        ans.append(new)
    return ans


def verify(data):
    need(type(data) is dict, "witness root must be an object")
    need(set(data) == {"version", "permutation_tensor", "small_cw2",
                       "basis_change", "outside_tensor"}, "witness fields")
    need(exact_int(data["version"]) and data["version"] == 1, "witness version")
    p = tensor(data["permutation_tensor"], (3, 3, 3))
    cw = tensor(data["small_cw2"], (3, 3, 3))
    outside = tensor(data["outside_tensor"], (3, 3, 3, 2))
    basis = parse_basis(data["basis_change"])

    singleton_ranks = [rank(flatten(p, (3, 3, 3), [i])) for i in range(3)]
    need(singleton_ranks == [3, 3, 3], "P must be concise in all three modes")
    equations, coordinates = linearized_rows(p)
    vector = [p.get(idx, 0) for idx in coordinates]
    need(len(equations) == 1134, "wrong appended-minor equation count")
    need(all(sum(a * b for a, b in zip(row, vector)) == 0 for row in equations),
         "L(P)P must vanish")
    lr = rank(equations)
    need(lr == 26, "appended-minor matrix must have rank 26")

    det = (0, 0)
    for perm in permutations(range(3)):
        term = (sign(perm), 0)
        for i in range(3):
            term = cmul(term, basis[i][perm[i]])
        det = cadd(det, term)
    need(det != (0, 0), "basis change is singular")
    for output in coordinates:
        value = (0, 0)
        for input_index, coefficient in p.items():
            term = (coefficient, 0)
            for mode in range(3):
                term = cmul(term, basis[output[mode]][input_index[mode]])
            value = cadd(value, term)
        need(value == (2 * cw.get(output, 0), 0), "L tensor-cubed P != 2 cw2")
    expected_cw = {}
    for i in (1, 2):
        for idx in ((0, i, i), (i, 0, i), (i, i, 0)):
            expected_cw[idx] = 1
    need(cw == expected_cw, "cw2 is not the six-term small CW tensor")

    need(len(outside) == 2, "outside witness must be a sum of two coordinate terms")
    qr = rank(flatten(outside, (3, 3, 3, 2), [3]))
    need(qr == 2, "outside witness must have D-flattening rank 2")
    balanced_ranks = [rank(flatten(outside, (3, 3, 3, 2), pair))
                      for pair in ([0, 1], [0, 2], [1, 2])]
    need(balanced_ranks == [2, 2, 2], "outside witness balanced flattenings")
    return {"status": "PASS", "field": "Q(i) embedded in C",
            "singleton_ranks": singleton_ranks,
            "appended_minor_matrix": [1134, 27], "appended_minor_rank": lr,
            "kernel_dimension": 27 - lr, "tangent_dimension": 27 + 27 - lr,
            "basis_determinant": list(det), "basis_image_scalar": 2,
            "outside_D_flattening_rank": qr,
            "outside_balanced_flattening_ranks": balanced_ranks,
            "scope": "geometry only; no asymptotic-rank upper bound checked"}


def main():
    controls = ("non_scalar_centroid", "wrong_p_coefficient", "wrong_cw2_coefficient",
                "singular_basis", "outside_inside_x", "boolean_coefficient",
                "unknown_schema_field")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--negative-control', choices=controls)
    control = parser.parse_args().negative_control
    root = Path(__file__).resolve().parent
    path = root / 'geometry_witness.json'
    if control:
        path = root / 'negative_controls' / (control + '.json')
    need(path.is_file() and path.stat().st_size <= 20000, "witness file invalid")
    try:
        data = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=no_duplicates,
                          parse_float=reject_number, parse_constant=reject_number)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        fail("cannot read witness: " + str(exc))
    print(json.dumps(verify(data), sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, TypeError, KeyError, IndexError, UnicodeError, RecursionError) as error:
        fail('verification input: ' + type(error).__name__)
