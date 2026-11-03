#!/usr/bin/env python3
"""Finite exact checks for tensor cores, threshold formulas, and rank witnesses."""
import argparse
from fractions import Fraction as F
import hashlib
from itertools import combinations, permutations, product
import json
from math import comb, gcd
from pathlib import Path

HERE = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise SystemExit('FAIL: ' + message)


def reject_number(value):
    raise SystemExit('FAIL: non-integer JSON number')


def pairs(items):
    result = {}
    for key, value in items:
        need(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def decode(raw):
    try:
        return json.loads(raw, object_pairs_hook=pairs, parse_float=reject_number,
                          parse_constant=reject_number)
    except (ValueError, UnicodeError):
        raise SystemExit('FAIL: malformed JSON')


def rational(value):
    need(type(value) is list and len(value) == 2 and all(type(x) is int for x in value),
         'rational encoding')
    num, den = value
    need(den > 0 and gcd(num, den) == 1, 'noncanonical rational')
    return F(num, den)


def expected_parameters():
    return [(n, s) for n in (3, 4, 5) for s in (F(1), F(-1), F(2, 3), F(-1, n))]


def load_cases(data):
    need(type(data) is dict and set(data) == {'schema', 'cases', 'threshold_ns'}, 'top-level fields')
    need(type(data['schema']) is int and data['schema'] == 1, 'schema')
    need(type(data['cases']) is list and len(data['cases']) == 12, 'case inventory')
    cases = []
    for record in data['cases']:
        need(type(record) is dict and set(record) == {'n', 's', 'coefficients'}, 'case fields')
        n = record['n']
        need(type(n) is int and n in (3, 4, 5), 'dimension range')
        s = rational(record['s'])
        need(s != 0, 'zero coupling is excluded')
        entries = record['coefficients']
        need(type(entries) is list and len(entries) == n**3, 'tensor shape')
        tensor = {index: rational(value) for index, value in zip(product(range(n), repeat=3), entries)}
        cases.append((n, s, tensor))
    need([(n, s) for n, s, _ in cases] == expected_parameters(), 'case parameter inventory')
    need(type(data['threshold_ns']) is list and all(type(n) is int for n in data['threshold_ns'])
         and data['threshold_ns'] == list(range(3, 13)) + [25], 'threshold inventory')
    return cases, data['threshold_ns']


def echelon(rows, ncols, reduced=False):
    basis = {}
    for source in rows:
        row = {i: F(v) for i, v in source.items() if v}
        need(all(type(i) is int and 0 <= i < ncols for i in row), 'matrix column bounds')
        for pivot in sorted(basis):
            coefficient = row.get(pivot, 0)
            if coefficient:
                for col, value in basis[pivot].items():
                    updated = row.get(col, F(0)) - coefficient * value
                    if updated:
                        row[col] = updated
                    else:
                        row.pop(col, None)
        if row:
            pivot = min(row)
            scale = row[pivot]
            basis[pivot] = {col: value / scale for col, value in row.items()}
    if reduced:
        for pivot in sorted(basis, reverse=True):
            for earlier in sorted(p for p in basis if p < pivot):
                row = basis[earlier]
                coefficient = row.get(pivot, 0)
                if coefficient:
                    for col, value in basis[pivot].items():
                        updated = row.get(col, F(0)) - coefficient * value
                        if updated:
                            row[col] = updated
                        else:
                            row.pop(col, None)
    return basis


def rank(rows, ncols):
    return len(echelon(rows, ncols))


def nullspace(rows, ncols):
    basis = echelon(rows, ncols, reduced=True)
    output = []
    for free in (i for i in range(ncols) if i not in basis):
        vector = {free: F(1)}
        for pivot, row in basis.items():
            if row.get(free, 0):
                vector[pivot] = -row[free]
        output.append(vector)
    need(len(output) + len(basis) == ncols, 'rank-nullity')
    for vector in output:
        need(all(sum((value * vector.get(col, 0) for col, value in row.items()), F(0)) == 0
                 for row in rows), 'nullspace certificate')
    return output


def flatten_rows(tensor, dims, left):
    left = tuple(left)
    right = tuple(i for i in range(len(dims)) if i not in left)
    left_indices = list(product(*(range(dims[i]) for i in left)))
    right_indices = list(product(*(range(dims[i]) for i in right)))
    li = {value: i for i, value in enumerate(left_indices)}
    ri = {value: i for i, value in enumerate(right_indices)}
    rows = [{} for _ in left_indices]
    for index, value in tensor.items():
        if value:
            rows[li[tuple(index[i] for i in left)]][ri[tuple(index[i] for i in right)]] = value
    return rows, len(right_indices)


def flatten_rank(tensor, dims, left):
    rows, ncols = flatten_rows(tensor, dims, left)
    return rank(rows, ncols)


def compatibility_rows(tensor, n, missing_modes=(0, 1, 2)):
    output = []
    for missing in missing_modes:
        others = tuple(i for i in range(3) if i != missing)
        pairs_ = list(product(range(n), repeat=2))
        pair_lookup = {indices: col for col, indices in enumerate(pairs_)}
        transposed_image, ncols = flatten_rows(tensor, (n, n, n), (missing,))
        need(ncols == n*n, 'image dimensions')
        annihilators = nullspace(transposed_image, n*n)
        for fixed in range(n):
            for annihilator in annihilators:
                row = {}
                for pair, col in pair_lookup.items():
                    if col in annihilator:
                        index = [0, 0, 0]
                        index[missing] = fixed
                        index[others[0]], index[others[1]] = pair
                        full_col = index[0]*n*n + index[1]*n + index[2]
                        row[full_col] = annihilator[col]
                output.append(row)
    return output


def check_core(n, s, tensor, missing_modes=(0, 1, 2)):
    need(s != 0, 'zero coupling is excluded')
    for index, value in tensor.items():
        expected = s + int(index[0] == index[1] == index[2])
        need(value == expected, 'tensor coefficient mismatch')
    modes = [flatten_rank(tensor, (n, n, n), (mode,)) for mode in range(3)]
    need(modes == [n, n, n], 'mode conciseness')
    equations = compatibility_rows(tensor, n, missing_modes)
    flat = [tensor[index] for index in product(range(n), repeat=3)]
    need(all(sum((value*flat[col] for col, value in row.items()), F(0)) == 0
             for row in equations), 'core not in compatibility kernel')
    kernel_dim = n**3 - rank(equations, n**3)
    need(kernel_dim == 1, 'compatibility kernel is not scalar')
    # Check the coefficient consequences after the slice-image calculation.
    kernels = nullspace(equations, n**3)
    need(len(kernels) == 1, 'kernel basis inventory')
    coefficients = [kernels[0].get(i, F(0)) for i in range(n**3)]
    q_values = []
    for k in range(n):
        values = {coefficients[i*n*n+j*n+k] for i in range(n) for j in range(n) if i != j}
        need(len(values) == 1, 'slice off-diagonal equality')
        q = next(iter(values))
        need(q == s*(sum(coefficients[i*n*n+i*n+k] for i in range(n))-n*q), 'coefficient equation (5)')
        q_values.append(q)
    need(len(set(q_values)) == 1, 'common slice value')
    q = q_values[0]
    need(all(coefficients[i*n*n+i*n+i] == (1+1/s)*q for i in range(n)), 'diagonal consequence')
    need(all(coefficients[i] == (q/s)*flat[i] for i in range(n**3)), 'kernel generator is not tensor multiple')
    return {'n': n, 's': [s.numerator, s.denominator], 'mode_ranks': modes,
            'compatibility_equation_count': len(equations), 'compatibility_rank': n**3-1,
            'compatibility_dimension': 1, 'coefficient_equations': 'PASS',
            'displayed_rank_upper_bound': n+1}


def integer_nth_root(value, exponent):
    need(type(value) is int and value >= 0 and type(exponent) is int and exponent >= 1, 'root arguments')
    low, high = 0, 1 << ((value.bit_length()+exponent-1)//exponent)
    while low+1 < high:
        middle = (low+high)//2
        if middle**exponent <= value:
            low = middle
        else:
            high = middle
    if high**exponent <= value:
        low = high
    need(low**exponent <= value < (low+1)**exponent, 'integer root certificate')
    return low


def cube_root_interval(value):
    denominator = 1 << 80
    lower = integer_nth_root(value*denominator**3, 3)
    low = F(lower, denominator)
    high = low if lower**3 == value*denominator**3 else F(lower+1, denominator)
    need(low**3 <= value <= high**3, 'outward radical interval')
    return low, high


def pair(value):
    return [value.numerator, value.denominator]


def check_threshold(n, wrong_premise=False, swap_radicals=False):
    need(type(n) is int and n >= 3, 'threshold dimension')
    N, R = n**n, (n+1)**n
    if wrong_premise:
        R = 2*N
    need(R > 2*N, 'speedup premise R>2N')
    low_u, high_u = cube_root_interval(N*N)
    low_v, high_v = cube_root_interval((R-N)**2)
    lower, upper = R+low_u-high_v, R+high_u-low_v
    if swap_radicals:
        lower, upper = R+low_v-high_u, R+high_v-low_u
    need(N < lower <= upper < R, 'threshold interval does not imply n<B_n<n+1')
    return {'n': n, 'N': N, 'R': R, 'R_minus_2N': R-2*N,
            'B_n_power_n_lower': pair(lower), 'B_n_power_n_upper': pair(upper),
            'N_less_than_lower_and_upper_less_than_R': True}


def permutation_core():
    return {index: F(1) for index in permutations(range(3))}


def embedded_seed(dims, active):
    result = {}
    for values, coefficient in permutation_core().items():
        index = [0]*len(dims)
        for mode, value in zip(active, values):
            index[mode] = value
        result[tuple(index)] = coefficient
    return result


def check_components():
    records = []
    for dims in ((3, 3, 3, 3), (3, 3, 3, 3, 2), (3, 2, 3, 2, 3, 3), (3, 3, 3, 3, 3, 3), (3, 3, 2, 2)):
        active = tuple(i for i, d in enumerate(dims) if d >= 3)
        triples = list(combinations(active, 3))
        need(len(triples) == comb(len(active), 3), 'triple count')
        seeds = {triple: embedded_seed(dims, triple) for triple in triples}
        for triple, seed in seeds.items():
            need([flatten_rank(seed, dims, (i,)) for i in range(len(dims))]
                 == [3 if i in triple else 1 for i in range(len(dims))], 'seed mode ranks')
            need(flatten_rank(seed, dims, triple) == 1, 'own triple flattening')
            for other in triples:
                if triple != other and set(triple) & set(other):
                    need(flatten_rank(seed, dims, other) == 3, 'overlapping triple separation')
        diagonal = {tuple([0]*len(dims)): F(1), tuple([1]*len(dims)): F(1)}
        for size in range(1, len(dims)):
            for cut in combinations(range(len(dims)), size):
                need(flatten_rank(diagonal, dims, cut) == 2, 'extra diagonal witness flattening')
        records.append({'dimensions': list(dims), 'active_factor_count': len(active),
                        'active_triples': len(triples), 'component_lower_bound_formula': len(triples)+1,
                        'all_seed_and_diagonal_flattening_checks': 'PASS'})
    core = permutation_core()
    tensor = {left+right: a*b for left, a in core.items() for right, b in core.items()}
    need(flatten_rank(tensor, (3,)*6, (0, 3)) == 9, 'disjoint triple product rank')
    return {'formats': records, 'disjoint_triple_mixed_flattening_rank': 9,
            'scope': 'finite witnesses and rank products only; no topological component proof'}


def check_boundary(corrupt=False):
    if corrupt:
        tensor = {(i, i//2, i%2): F(1) for i in range(4)}
        need(flatten_rank(tensor, (9, 3, 2), (0,)) <= 3, 'boundary flattening exceeds three')
        return None
    embedding = [[F(1), F(i), F(i*i)] for i in range(9)]
    right = [[F(1), F(1), F(0)], [F(0), F(1), F(1)], [F(0), F(0), F(1)]]
    eigenvalues = [F(1), F(2), F(3)]
    tensor = {}
    for i, j, k in product(range(9), range(3), range(2)):
        tensor[(i, j, k)] = sum((embedding[i][h]*right[h][j]*(1 if k == 0 else eigenvalues[h])
                                  for h in range(3)), F(0))
    modes = [flatten_rank(tensor, (9, 3, 2), (i,)) for i in range(3)]
    need(modes == [3, 3, 2], 'boundary sample mode ranks')
    need(len(set(eigenvalues)) == 3, 'pencil simple spectrum')
    return {'dimensions': [9, 3, 2], 'explicit_rank_one_summands': 3,
            'mode_ranks': modes, 'simple_spectrum': [pair(x) for x in eigenvalues],
            'scope': 'one exact dense pencil/embedding example; no finite proof of density or irreducibility'}


CONTROLS = ('duplicate-key', 'float', 'boolean-dimension', 'zero-denominator', 'unknown-field',
            'bad-shape', 'zero-coupling', 'omitted-two-images', 'damaged-coefficient',
            'threshold-premise', 'threshold-swapped-radicals', 'boundary-rank-four')


def negative(control, raw):
    if control == 'duplicate-key':
        decode('{"schema":1,"schema":1}')
    elif control == 'float':
        decode('{"s":1.0}')
    elif control in ('boolean-dimension', 'zero-denominator', 'unknown-field', 'bad-shape', 'zero-coupling'):
        data = decode(raw)
        if control == 'boolean-dimension':
            data['cases'][0]['n'] = True
        elif control == 'zero-denominator':
            data['cases'][0]['s'] = [1, 0]
        elif control == 'unknown-field':
            data['unexpected'] = 1
        elif control == 'bad-shape':
            data['cases'][0]['coefficients'].pop()
        else:
            data['cases'][0]['s'] = [0, 1]
        load_cases(data)
    elif control in ('omitted-two-images', 'damaged-coefficient'):
        cases, _ = load_cases(decode(raw))
        n, s, tensor = cases[0]
        if control == 'damaged-coefficient':
            tensor[(0, 0, 1)] += 1
        check_core(n, s, tensor, (0,) if control == 'omitted-two-images' else (0, 1, 2))
    elif control in ('threshold-premise', 'threshold-swapped-radicals'):
        check_threshold(3, control == 'threshold-premise', control == 'threshold-swapped-radicals')
    elif control == 'boundary-rank-four':
        check_boundary(True)
    raise SystemExit('FAIL: negative control unexpectedly accepted')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--negative-control', choices=CONTROLS)
    args = parser.parse_args()
    fixture = HERE / 'CASES.json'
    need(fixture.is_file() and not fixture.is_symlink() and fixture.stat().st_size <= 500000, 'fixture file')
    raw = fixture.read_bytes()
    if args.negative_control:
        negative(args.negative_control, raw)
    cases, ns = load_cases(decode(raw))
    results = [check_core(n, s, tensor) for n, s, tensor in cases]
    diagonal_results = []
    for n in (3, 4, 5):
        tensor = {index: F(int(index[0] == index[1] == index[2])) for index in product(range(n), repeat=3)}
        dimension = n**3-rank(compatibility_rows(tensor, n), n**3)
        need(dimension == n, 'diagonal kernel reference')
        diagonal_results.append({'n': n, 'diagonal_compatibility_dimension': dimension})
    report = {'status': 'PASS_FINITE_CORROBORATION', 'arithmetic': 'stdlib Fraction and certified integer-root intervals',
        'fixture_sha256': hashlib.sha256(raw).hexdigest(), 'core_cases': results,
        'diagonal_border_obstruction_references': diagonal_results,
        'threshold_cases': [check_threshold(n) for n in ns], 'components': check_components(),
        'boundary': check_boundary(),
        'scope': 'Only the listed finite rational cases. The asymptotic speedup theorem, the all-n proof, Zariski closure, density, and irreducibility are not certified here.'}
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
