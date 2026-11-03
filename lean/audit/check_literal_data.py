#!/usr/bin/env python3
"""Check the literal tables and reference certificates with exact arithmetic."""
import ast
import itertools
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent


def need(ok, message):
    if not ok:
        raise SystemExit('FAIL: ' + message)


def reject_number(value):
    raise SystemExit('FAIL: noninteger JSON number')


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON member')
        result[key] = value
    return result


def load(name):
    data = json.loads((ROOT/'certificate'/name).read_text(),
                      object_pairs_hook=unique_pairs,
                      parse_float=reject_number, parse_constant=reject_number)
    def exact(value):
        if type(value) is dict:
            for item in value.values():
                exact(item)
        elif type(value) is list:
            for item in value:
                exact(item)
        else:
            need(type(value) in (str, int), 'nonexact JSON scalar')
    exact(data)
    return data


def literal(source, start, stop):
    need(source.count(start) == 1, 'literal start anchor')
    body = source.split(start, 1)[1].split(stop, 1)[0].strip()
    need(re.fullmatch(r'[!\[\]0-9,\s-]+', body) is not None, 'literal syntax')
    return ast.literal_eval(body.replace('!', ''))


def tensor(raw):
    result = {}
    for indices, value in raw:
        need(type(value) is int and all(type(i) is int for i in indices), 'tensor integers')
        key = tuple(indices)
        need(key not in result, 'duplicate tensor coordinate')
        result[key] = value
    return result


def check_geometry(data, source):
    need(set(data) == {'version', 'permutation_tensor', 'small_cw2',
                       'basis_change', 'outside_tensor'}, 'geometry fields')
    need(type(data['version']) is int and data['version'] == 1, 'geometry version')
    need(tensor(data['permutation_tensor']) ==
         {p: 1 for p in itertools.permutations(range(3))}, 'permutation tensor')
    expected = {}
    for i in (1, 2):
        for p in ((0, i, i), (i, 0, i), (i, i, 0)):
            expected[p] = 1
    need(tensor(data['small_cw2']) == expected, 'cw2 tensor')
    need(tensor(data['outside_tensor']) == {(0, 0, 0, 0): 1, (1, 1, 1, 1): 1},
         'outside tensor')
    need(data['basis_change'] == [[[1,0],[0,0],[0,0]], [[0,0],[1,0],[1,0]],
                                   [[0,0],[0,1],[0,-1]]], 'Gaussian basis')
    rows = literal(source, 'def rows4 : Fin 126 → Fin 4 → Fin 9 :=', '/--')
    need(rows == [list(p) for p in itertools.combinations(range(9), 4)], 'minor row table')


def check_exchange(data, source):
    main = [g for g in range(64) if all((g//(4**j)) % 4 for j in range(3))]
    inner = [g for g in main if (g ^ 21) in main]
    residual = [g for g in range(64) if g not in main and (g ^ 21) not in main]
    labels = [['A', g] for g in main] + [['H', 21]] + [['B', g] for g in residual]
    need(data['target_labels'] == labels, 'exchange target labels')
    need(data['source_dimension'] == 73 and data['target_dimension'] == 46
         and data['coefficient_scale'] == 64, 'exchange dimensions')
    rows = []
    for kind, mask in labels:
        row = [(-1) ** ((mask & g).bit_count()) for g in range(64)]
        row += [-1 if kind == 'H' else 0]
        row += [1 if kind == 'A' and mask == g else 0 for g in inner]
        rows.append(row)
    need(data['row_matrix'] == rows, 'exchange row matrix')
    need(data['row_degrees'] == [0]*27+[-2]+[1]*18, 'exchange row degrees')
    terms = {(g,g,g): 1 for g in range(64)}
    for i, g in enumerate(inner):
        for j, h in enumerate(inner):
            if g ^ h == 21:
                for p in ((64,65+i,65+j),(65+i,64,65+j),(65+i,65+j,64)):
                    terms[p] = 64
    need({tuple(t[:3]): t[3] for t in data['source_terms_scaled']} == terms
         and len(data['source_terms_scaled']) == 88, 'scaled source tensor')
    table = [0]*64
    for i, g in enumerate([g for g in residual if g < (g ^ 21)], 1):
        table[g] = i
        table[g ^ 21] = -i
    actual = literal(source, 'def residualWeightTable : Fin 64 → ℤ :=', '\ndef tightWeight')
    need(actual == table, 'tight weight table')
    need(data['tight_C18_weights'] == [0]+[table[g] for g in residual], 'tight certificate weights')


def main():
    geometry = load('geometry_witness.json')
    exchange = load('certificate.json')
    control = sys.argv[1:]
    need(not control or control in (['--wrong-geometry'], ['--wrong-exchange']), 'arguments')
    if control == ['--wrong-geometry']:
        geometry['permutation_tensor'][0][1] = 2
    if control == ['--wrong-exchange']:
        exchange['row_matrix'][27][64] = 0
    check_geometry(geometry, (ROOT/'TR23/GeometryDefinitions.lean').read_text())
    check_exchange(exchange, (ROOT/'TR23/ExchangeDefinitions.lean').read_text())
    need(not control, 'accepted literal-data control')
    print('PASS: geometry literals, 126 minor rows, exchange map and tight weights')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, TypeError, KeyError, SyntaxError, UnicodeError):
        raise SystemExit('FAIL: invalid literal-data input')
