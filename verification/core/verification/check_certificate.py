#!/usr/bin/env python3
"""Dense integer-only verification of the Laurent tensor certificate.

The expected tensors are reconstructed from their mathematical definitions.
All rejection paths use explicit SystemExit; behavior is unchanged under -O.
"""
import argparse
import copy
import itertools
import json
from collections import Counter, defaultdict
from pathlib import Path


def fail(message):
    raise SystemExit('FAIL: ' + message)


def need(condition, message):
    if not condition:
        fail(message)


def integer(x):
    return type(x) is int


def reject_number(value):
    fail('non-integer JSON number: ' + value)


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def sparse_tensor(raw, dim, name):
    need(type(raw) is list, name + ' is not a list')
    result = {}
    for term in raw:
        need(type(term) is list and len(term) == 4 and all(integer(x) for x in term),
             name + ' has malformed term')
        i, j, k, value = term
        need(all(0 <= x < dim for x in (i, j, k)) and value != 0,
             name + ' has bad index or zero coefficient')
        need((i, j, k) not in result, name + ' has duplicate term')
        result[i, j, k] = value
    return result


def poly(raw, name):
    need(type(raw) is list, name + ' is not a polynomial list')
    result = {}
    for term in raw:
        need(type(term) is list and len(term) == 2 and all(integer(x) for x in term),
             name + ' has malformed coefficient')
        degree, value = term
        need(-3 <= degree <= 3 and value != 0 and degree not in result,
             name + ' has invalid degree, zero, or duplicate')
        result[degree] = value
    return result


def border_check(raw):
    need(type(raw) is list and len(raw) == 10, 'border decomposition must have ten terms')
    family = defaultdict(int)
    for index, term in enumerate(raw):
        need(type(term) is dict and set(term) == {'scalar', 'vector'},
             'border term fields')
        scalar = poly(term['scalar'], 'border scalar')
        need(type(term['vector']) is list and len(term['vector']) == 9,
             'border vector length')
        vector = [poly(p, 'border vector entry') for p in term['vector']]
        for i, j, k in itertools.product(range(9), repeat=3):
            for (d, s), (di, vi), (dj, vj), (dk, vk) in itertools.product(
                    scalar.items(), vector[i].items(), vector[j].items(), vector[k].items()):
                family[d + di + dj + dk, i, j, k] += s * vi * vj * vk
    family = {key: value for key, value in family.items() if value}
    expected = {}
    # Diagonal small CW8: one head and two equal nonhead coordinates.
    for i, j, k in itertools.product(range(9), repeat=3):
        coords = (i, j, k)
        heads = coords.count(0)
        if heads == 1:
            others = [x for x in coords if x]
            if others[0] == others[1]:
                expected[0, i, j, k] = 1
            expected[1, i, j, k] = -1
        elif heads == 0:
            if i == j == k:
                expected[1, i, j, k] = 1
            expected[3, i, j, k] = -1
    need(family == expected, 'CW8 Laurent identity differs from its exact expansion')
    return len(family)


def verify(cert):
    need(type(cert) is dict, 'certificate is not an object')
    need(set(cert) == {'schema', 'source_dimension', 'target_dimension', 'coefficient_scale',
                      'source_terms_scaled', 'target_labels', 'row_degrees', 'row_matrix',
                      'constant_target_scaled', 'tight_C18_weights', 'border_CW8_terms'},
         'certificate fields')
    need(cert['schema'] == 'tr23-cw2-strict-upper-v1', 'schema mismatch')
    for key, value in [('source_dimension', 73), ('target_dimension', 46), ('coefficient_scale', 64)]:
        need(integer(cert[key]) and cert[key] == value, key + ' mismatch')

    # Independent construction with three-coordinate tuples.
    group = list(itertools.product(range(4), repeat=3))
    encode = lambda t: t[0] + 4 * t[1] + 16 * t[2]
    decode = lambda n: (n % 4, (n // 4) % 4, n // 16)
    main_ids = sorted(encode(t) for t in group if 0 not in t)
    common_ids = sorted(encode(t) for t in group if all(x in (2, 3) for x in t))
    main_set = set(main_ids)
    residual_ids = sorted(n for n in range(64) if n not in main_set and (n ^ 21) not in main_set)
    need((len(main_ids), len(common_ids), len(residual_ids)) == (27, 8, 18), 'set sizes')
    need(0 not in residual_ids and 21 in main_ids and 21 not in common_ids, 'head exclusions')
    for values in (common_ids, residual_ids):
        need(all((x ^ 21) in values and (x ^ 21) != x for x in values), 'translation pairs')
    labels = [['A', x] for x in main_ids] + [['H', 21]] + [['B', x] for x in residual_ids]
    need(type(cert['target_labels']) is list
         and all(type(x) is list and len(x) == 2 and type(x[0]) is str
                 and integer(x[1]) for x in cert['target_labels']), 'coordinate label types')
    need(cert['target_labels'] == labels, 'coordinate labels differ')
    degrees = cert['row_degrees']
    need(type(degrees) is list and all(integer(d) for d in degrees)
         and degrees == [0] * 27 + [-2] + [1] * 18, 'row degrees differ')
    rows = cert['row_matrix']
    need(type(rows) is list and len(rows) == 46, 'matrix row count')
    for row in rows:
        need(type(row) is list and len(row) == 73 and all(integer(v) and -1 <= v <= 1 for v in row),
             'matrix row shape or integer entries')
    # Do not simply trust the displayed matrix: its entries are allowed to
    # vary here, and the tensor contraction below decides if it works.

    source = sparse_tensor(cert['source_terms_scaled'], 73, 'source')
    expected_source = {(g, g, g): 1 for g in range(64)}
    for left in range(8):
        for right in range(8):
            if common_ids[left] ^ common_ids[right] == 21:
                # Head may occupy any of the three places; ordered left/right
                # already supplies the other factor of two.
                u, v = 65 + left, 65 + right
                for triple in [(64, u, v), (u, 64, v), (u, v, 64)]:
                    expected_source[triple] = 64
    need(source == expected_source and len(source) == 88, 'source is not scaled D64 plus paired CW8')

    target = sparse_tensor(cert['constant_target_scaled'], 46, 'target')
    expected_target = {}
    tight_support = []
    for i, j, k in itertools.product(range(46), repeat=3):
        kinds = (labels[i][0], labels[j][0], labels[k][0])
        if kinds == ('A', 'A', 'A'):
            digits = [decode(labels[n][1]) for n in (i, j, k)]
            if all({digits[0][d], digits[1][d], digits[2][d]} == {1, 2, 3}
                   for d in range(3)):
                expected_target[i, j, k] = 64
        elif kinds.count('H') == 1 and kinds.count('B') == 2:
            residuals = [labels[n][1] for n in (i, j, k) if labels[n][0] == 'B']
            if residuals[0] ^ residuals[1] == 21:
                expected_target[i, j, k] = 64
                tight_support.append((i - 27, j - 27, k - 27))
    need(target == expected_target and len(target) == 270, 'target differs from P^3 plus paired CW18')

    source_list = [(*indices, value) for indices, value in source.items()]
    degree_counts = Counter()
    for i, j, k in itertools.product(range(46), repeat=3):
        degree = degrees[i] + degrees[j] + degrees[k]
        degree_counts[degree] += 1
        # This sums every source term, for every ordered output coordinate.
        coefficient = sum(value * rows[i][u] * rows[j][v] * rows[k][w]
                          for u, v, w, value in source_list)
        if degree < 0:
            need(coefficient == 0, 'nonzero negative Laurent coefficient at ' + str((i, j, k, degree)))
        elif degree == 0:
            need(coefficient == target.get((i, j, k), 0),
                 'constant Laurent coefficient mismatch at ' + str((i, j, k)))

    # The theorem requires injective integer labels in EACH mode.
    weights = cert['tight_C18_weights']
    need(type(weights) is list and len(weights) == 19 and all(integer(x) for x in weights),
         'tight weights shape')
    need(set(weights) == set(range(-9, 10)) and weights[0] == 0, 'tight weights not injective as required')
    need(len(tight_support) == 54, 'tight support size')
    marginals = [Counter() for _ in range(3)]
    for triple in tight_support:
        need(sum(weights[x] for x in triple) == 0, 'tight support equation fails')
        for mode, coordinate in enumerate(triple):
            marginals[mode][coordinate] += 1
    for counts in marginals:
        need(dict(counts) == {0: 18, **{j: 2 for j in range(1, 19)}}, 'uniform support marginal counts')
    need(81 > 4 ** 3 and 62 < 4 ** 3 and 81 < 5 ** 3, 'strict integer comparisons')
    border_count = border_check(cert['border_CW8_terms'])
    return {'checked_output_coefficients': 46 ** 3, 'source_terms': len(source),
            'constant_target_terms': len(target),
            'Laurent_degree_counts': dict(sorted(degree_counts.items())),
            'CW8_nonzero_expanded_coefficients': border_count,
            'tight_support_terms': len(tight_support)}


def control_cases(cert):
    cases = []
    damaged = copy.deepcopy(cert)
    damaged['row_matrix'][27][64] = 0
    cases.append(('removed_auxiliary_pole_cancellation', damaged))
    damaged = copy.deepcopy(cert)
    damaged['constant_target_scaled'][0][3] = 63
    cases.append(('changed_target_coefficient', damaged))
    damaged = copy.deepcopy(cert)
    damaged['border_CW8_terms'][-1]['scalar'][1][1] = -7
    cases.append(('changed_border_scalar_cancellation', damaged))
    damaged = copy.deepcopy(cert)
    damaged['tight_C18_weights'][1] = damaged['tight_C18_weights'][2]
    cases.append(('noninjective_tight_labels', damaged))
    return cases


def controls(cert):
    cases = control_cases(cert)
    rejected = []
    for name, data in cases:
        try:
            verify(data)
        except SystemExit as exc:
            need(str(exc).startswith('FAIL: '), 'negative control failed for unexpected reason')
            rejected.append({'name': name, 'reason': str(exc)})
        else:
            fail('accepted negative control: ' + name)
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--negative-control', choices=(
        'removed_auxiliary_pole_cancellation', 'changed_target_coefficient',
        'changed_border_scalar_cancellation', 'noninjective_tight_labels'))
    control = parser.parse_args().negative_control
    path = Path(__file__).resolve().with_name('certificate.json')
    try:
        cert = json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=unique_pairs,
                          parse_float=reject_number, parse_constant=reject_number)
    except (OSError, ValueError, UnicodeError) as exc:
        fail('cannot read certificate: ' + str(exc))
    if control:
        verify(dict(control_cases(cert))[control])
        fail('accepted negative control: ' + control)
    result = verify(cert)
    result['negative_controls'] = controls(cert)
    result['status'] = 'PASS'
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, TypeError, KeyError, IndexError, UnicodeError, RecursionError) as error:
        fail('verification input: ' + type(error).__name__)
