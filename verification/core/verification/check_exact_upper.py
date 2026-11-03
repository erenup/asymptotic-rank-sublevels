#!/usr/bin/env python3
"""Sparse integer/rational checks for the TR-23 strict upper bound.

This checks identities and finite hypotheses only. It does not replace the
classical tight-support or asymptotic-spectrum theorems.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
from itertools import permutations, product
import json


def fail(message):
    raise SystemExit('FAIL: '+message)


def add(table, key, value):
    table[key] += value
    if table[key] == 0:
        del table[key]


def digits(g):
    return (g & 3, (g >> 2) & 3, (g >> 4) & 3)


def determinant(matrix):
    a = [[Fraction(x) for x in row] for row in matrix]
    sign = 1
    value = Fraction(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != j:
            a[pivot], a[j] = a[j], a[pivot]
            sign *= -1
        p = a[j][j]
        value *= p
        for i in range(j+1, len(a)):
            scale = a[i][j]/p
            for k in range(j, len(a)):
                a[i][k] -= scale*a[j][k]
    return sign*value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--negative-control', choices=('wrong_cancellation',
        'missing_group_term', 'wrong_fourier_scale', 'label_collision',
        'wrong_marginal'))
    mutation = parser.parse_args().negative_control
    group = set(range(64))
    s = {g for g in group if all(d != 0 for d in digits(g))}
    a = 1 + 4 + 16
    shifted = {g ^ a for g in s}
    inside = s & shifted
    residual = group - (s | shifted)
    if (len(s), len(inside), len(residual)) != (27, 8, 18):
        fail('wrong group-set sizes')
    if any(g ^ a not in q for q in (inside, residual) for g in q):
        fail('paired sets are not translation invariant')
    if 0 in (s | residual) or a not in s or a in inside:
        fail('special indices violate the extraction hypotheses')

    # Character orthogonality verifies the 64-term Walsh rank decomposition.
    normalization = 63 if mutation == 'wrong_fourier_scale' else 64
    for h in sorted(group):
        total = sum((-1)**((chi & h).bit_count() % 2) for chi in group)
        if Fraction(total, normalization) != int(h == 0):
            fail('Walsh decomposition coefficient differs from the group tensor')

    base = ('z0', 0)
    def images(g):
        result = []
        if g in s:
            result.append((0, ('x', g)))
        if g == a:
            result.append((-2, base))
        if g in residual:
            result.append((1, ('z', g)))
        return result

    output = defaultdict(int)
    removed = False
    for u, v in product(sorted(group), repeat=2):
        w = u ^ v
        if mutation == 'missing_group_term' and not removed and u in s and v in s and w in s:
            removed = True
            continue
        for terms in product(images(u), images(v), images(w)):
            exponent = sum(term[0] for term in terms)
            labels = tuple(term[1] for term in terms)
            add(output, (exponent, labels), 1)

    # The extra direct summand has one base coordinate in every monomial.
    sign = 1 if mutation == 'wrong_cancellation' else -1
    for g in sorted(inside):
        for base_position in range(3):
            labels = [('x', g), ('x', g ^ a)]
            labels.insert(base_position, base)
            add(output, (-2, tuple(labels)), sign)
    if any(exponent < 0 for exponent, labels in output):
        fail('a negative Laurent coefficient survives CW8 cancellation')

    # Build the proposed constant coefficient independently from P^3 and CW18.
    target = defaultdict(int)
    for triples in product(list(permutations((1, 2, 3))), repeat=3):
        coordinates = [sum(triples[j][k] << (2*j) for j in range(3)) for k in range(3)]
        add(target, tuple(('x', g) for g in coordinates), 1)
    cw_support = set()
    for g in sorted(residual):
        for base_position in range(3):
            labels = [('z', g), ('z', g ^ a)]
            labels.insert(base_position, base)
            add(target, tuple(labels), 1)
            cw_support.add(tuple(labels))
    actual = {labels: value for (exponent, labels), value in output.items() if exponent == 0}
    if actual != dict(target) or len(actual) != 270 or len(cw_support) != 54:
        fail('constant coefficient is not the claimed direct sum')

    # Independently expand the ten rank-one terms of the CW8 degeneration.
    q = 8
    family = defaultdict(int)
    vectors = [[(0, 0), (1, i)] for i in range(1, q+1)]
    vectors.append([(0, 0)] + [(1, i) for i in range(1, q+1)])
    vectors.append([(0, 0)])
    coefficients = [1]*q + [-1, -(q-1)]
    for vector, coefficient in zip(vectors, coefficients):
        for terms in product(vector, repeat=3):
            add(family, (sum(t[0] for t in terms)-2, tuple(t[1] for t in terms)), coefficient)
    if any(exponent < 0 for exponent, labels in family):
        fail('CW8 rank-ten family has negative powers')
    matrix = [[int(i == j)-1 for j in range(q)] for i in range(q)]
    expected = defaultdict(int)
    for i, j in product(range(1, q+1), repeat=2):
        for base_position in range(3):
            labels = [i, j]
            labels.insert(base_position, 0)
            add(expected, tuple(labels), matrix[i-1][j-1])
    constant = {labels: value for (exponent, labels), value in family.items() if exponent == 0}
    if constant != dict(expected) or determinant(matrix) != -7:
        fail('CW8 constant quadratic form is not the required nonsingular form')

    # Also check the diagonal formula in the proof.
    diagonal_family = defaultdict(int)
    for i in range(1, q+1):
        for terms in product([(0, 0), (1, i)], repeat=3):
            add(diagonal_family, (sum(t[0] for t in terms)-2,
                tuple(t[1] for t in terms)), 1)
    for terms in product([(0, 0)]+[(2, i) for i in range(1, q+1)], repeat=3):
        add(diagonal_family, (sum(t[0] for t in terms)-3,
            tuple(t[1] for t in terms)), -1)
    add(diagonal_family, (-3, (0, 0, 0)), 1)
    add(diagonal_family, (-2, (0, 0, 0)), -q)
    diagonal_expected = {}
    for i in range(1, q+1):
        for base_position in range(3):
            labels = [i, i]
            labels.insert(base_position, 0)
            diagonal_expected[tuple(labels)] = 1
    if any(exponent < 0 for exponent, labels in diagonal_family):
        fail('diagonal CW8 rank-ten family has negative powers')
    if {labels: value for (exponent, labels), value in diagonal_family.items()
            if exponent == 0} != diagonal_expected:
        fail('diagonal CW8 constant term differs from the diagonal tensor')

    # Tightness and the exact rational marginal distribution.
    pairs = sorted((g, g ^ a) for g in residual if g < (g ^ a))
    weights = {base: 0}
    for j, (g, h) in enumerate(pairs, 1):
        weights[('z', g)] = j
        weights[('z', h)] = -j
    if mutation == 'label_collision':
        weights[('z', pairs[0][0])] = 0
    if len(weights) != 19 or len(set(weights.values())) != 19:
        fail('tight labels are not injective')
    if any(sum(weights[label] for label in term) for term in cw_support):
        fail('support term does not have tight weight zero')
    marginals = [defaultdict(Fraction) for _ in range(3)]
    denominator = 55 if mutation == 'wrong_marginal' else 54
    for term in cw_support:
        for mode, label in enumerate(term):
            marginals[mode][label] += Fraction(1, denominator)
    for marginal in marginals:
        if sum(marginal.values()) != 1 or marginal[base] != Fraction(1, 3):
            fail('CW18 marginal does not have the claimed probability mass')
        if any(marginal[label] != Fraction(1, 27) for label in weights if label != base):
            fail('CW18 nonbase marginal differs from 1/27')
    # exp(3H)=3*27^2=(3*cuberoot81)^3; Q>12 is an integer comparison.
    entropy_base_cubed = 3*27**2
    if entropy_base_cubed != 27*81 or entropy_base_cubed <= 12**3 or 74-12 != 62 or 62 >= 4**3:
        fail('exact final strict inequalities fail')
    print(json.dumps(dict(status='PASS', group_order=64,
        set_sizes=[27, 8, 18], constant_support=270,
        cw8_rank_one_terms=len(vectors), cw8_quadratic_determinant=-7,
        cw8_diagonal_formula='PASS',
        cw18_tight_support_size=54, entropy_exponential_cubed=entropy_base_cubed,
        scope='Exact finite identities and theorem hypotheses only; external classical theorems remain required.'), sort_keys=True))


if __name__ == '__main__':
    main()
