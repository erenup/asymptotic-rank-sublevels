#!/usr/bin/env python3
"""Check file bindings and finite exact checks in three interpreter modes."""
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).absolute().parent
ROOT = HERE.parent
MODES = [('normal', [], '1'), ('optimized', ['-O'], '1'), ('hash-seed', [], '8675309')]
PROOF_FILES = {'DIRECTIONS.md', 'COMPONENT_DERIVATION.md', 'MERGING_BOUNDARY.md', 'CHECKS.md'}
VERIFICATION_FILES = {
    'README.md', 'run.py', 'check_components.py', 'CASES.json',
    'CHECKERS.txt', 'NEGATIVE_CONTROLS.json', 'SHA256SUMS',
}
EXPECTED_CONTROLS = {
    'duplicate-key': 'FAIL: duplicate JSON key\n',
    'float': 'FAIL: non-integer JSON number\n',
    'boolean-dimension': 'FAIL: dimension range\n',
    'zero-denominator': 'FAIL: noncanonical rational\n',
    'unknown-field': 'FAIL: top-level fields\n',
    'bad-shape': 'FAIL: tensor shape\n',
    'zero-coupling': 'FAIL: zero coupling is excluded\n',
    'omitted-two-images': 'FAIL: compatibility kernel is not scalar\n',
    'damaged-coefficient': 'FAIL: tensor coefficient mismatch\n',
    'threshold-premise': 'FAIL: speedup premise R>2N\n',
    'threshold-swapped-radicals': 'FAIL: threshold interval does not imply n<B_n<n+1\n',
    'boundary-rank-four': 'FAIL: boundary flattening exceeds three\n',
}
IMPORTS = {
    'run.py': {'ast', 'hashlib', 'json', 'os', 'pathlib', 're', 'subprocess', 'sys'},
    'check_components.py': {'argparse', 'fractions', 'hashlib', 'itertools', 'json', 'math', 'pathlib'},
}
FORBIDDEN_CALLS = {'float', 'complex', 'eval', 'exec', 'compile', '__import__', 'getattr'}


def need(ok, message):
    if not ok:
        raise SystemExit('FAIL: '+message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def reject_number(value):
    raise SystemExit('FAIL: non-integer JSON number')


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def read_json(data):
    return json.loads(data, object_pairs_hook=unique_pairs,
                      parse_float=reject_number, parse_constant=reject_number)


def inventory():
    need(ROOT.is_dir() and not ROOT.is_symlink(), 'invalid components directory')
    files = {}
    for directory, expected in [('proofs', PROOF_FILES), ('verification', VERIFICATION_FILES)]:
        root = ROOT/directory
        need(root.is_dir() and not root.is_symlink(), 'invalid '+directory+' directory')
        paths = list(root.iterdir())
        need({path.name for path in paths} == expected, directory+' inventory')
        for path in paths:
            name = directory+'/'+path.name
            need(not path.is_symlink(), 'symbolic link: '+name)
            need(path.is_file(), 'nonregular file: '+name)
            need(path.stat().st_size <= 500000, 'file size: '+name)
            files[name] = path.read_bytes()
    return files


def validate_manifest(files):
    manifest = 'verification/SHA256SUMS'
    entries = {}
    for line in files[manifest].decode().splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  ((?:proofs|verification)/[A-Za-z][A-Za-z0-9_.-]*)', line)
        need(match is not None, 'manifest syntax or path')
        sha, name = match.groups()
        need(name not in entries, 'duplicate manifest entry')
        entries[name] = sha
    need(set(entries) == set(files)-{manifest}, 'manifest coverage')
    for name, sha in entries.items():
        need(digest(files[name]) == sha, 'manifest mismatch: '+name)


def validate_python(files):
    for name, allowed in IMPORTS.items():
        tree = ast.parse(files['verification/'+name].decode(), filename=name)
        for node in ast.walk(tree):
            need(not isinstance(node, ast.Assert), 'assert in '+name)
            if isinstance(node, ast.ImportFrom):
                need(node.level == 0 and node.module, 'relative import in '+name)
                need(node.module in allowed, 'unexpected import in '+name)
                if node.module == 'math':
                    need(all(item.name in {'comb', 'gcd'} for item in node.names), 'non-integer math import')
            elif isinstance(node, ast.Import):
                need(all(item.name in allowed for item in node.names), 'unexpected import in '+name)
            need(not (isinstance(node, ast.Constant) and type(node.value).__name__ in {'float', 'complex'}),
                 'inexact literal in '+name)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                need(node.func.id not in FORBIDDEN_CALLS, 'inexact or dynamic call in '+name)
            if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                    and isinstance(node.func.value, ast.Name) and node.func.value.id == 'math'):
                need(node.func.attr in {'comb', 'gcd'}, 'non-integer math call')


def validate_registry(data):
    registry = {}
    for line in data.decode().splitlines():
        match = re.fullmatch(r'(check_components\.py) ([0-9a-f]{64})', line)
        need(match is not None, 'checker registry syntax or path')
        name, sha = match.groups()
        need(name not in registry, 'duplicate checker')
        registry[name] = sha
    need(set(registry) == {'check_components.py'}, 'checker registry coverage')
    return registry


def validate_controls(data):
    controls = read_json(data)
    need(type(controls) is dict and set(controls) == {'check_components.py'}, 'negative-control coverage')
    entries = controls['check_components.py']
    need(type(entries) is list, 'negative-control list')
    registered = {}
    for entry in entries:
        need(type(entry) is dict and set(entry) == {'name', 'stderr'}, 'negative-control fields')
        name, error = entry['name'], entry['stderr']
        need(type(name) is str and name in EXPECTED_CONTROLS, 'negative-control name')
        need(name not in registered, 'duplicate negative control')
        need(type(error) is str and error == EXPECTED_CONTROLS[name], 'negative-control diagnostic')
        registered[name] = error
    need(registered == EXPECTED_CONTROLS, 'negative-control inventory')
    return registered


def validate_directory():
    files = inventory()
    validate_manifest(files)
    validate_python(files)
    for name, data in files.items():
        if name.endswith('.json'):
            read_json(data)
    registry = validate_registry(files['verification/CHECKERS.txt'])
    controls = validate_controls(files['verification/NEGATIVE_CONTROLS.json'])
    return registry, controls, {name: digest(data) for name, data in files.items()}


def execute(command, seed, label):
    env = {'PATH': os.defpath, 'LC_ALL': 'C.UTF-8', 'PYTHONHASHSEED': seed}
    try:
        return subprocess.run(command, cwd=HERE, env=env, stdin=subprocess.DEVNULL,
                              capture_output=True, timeout=600)
    except subprocess.TimeoutExpired:
        raise SystemExit('FAIL: checker timeout: '+label)


def main():
    need(len(sys.argv) == 1, 'unexpected runner argument')
    registry, controls, before = validate_directory()
    previous = None
    negative_runs = 0
    for name, expected in sorted(registry.items()):
        for mode, flags, seed in MODES:
            command = [sys.executable, '-S', '-s', '-B']+flags+[str(HERE/name)]
            result = execute(command, seed, name+' '+mode)
            need(result.returncode == 0, 'checker exit status: '+mode)
            need(not result.stderr, 'checker standard error: '+mode)
            need(digest(result.stdout) == expected, 'output hash mismatch: '+mode)
            need(previous is None or previous == result.stdout, 'mode mismatch')
            previous = result.stdout
            for control, diagnostic in sorted(controls.items()):
                label = mode+' '+control
                result = execute(command+['--negative-control', control], seed, label)
                need(result.returncode == 1, 'negative-control exit status: '+label)
                need(not result.stdout, 'negative-control standard output: '+label)
                need(result.stderr == diagnostic.encode(), 'negative-control error: '+label)
                negative_runs += 1
        print('PASS: '+name+' (normal, optimized, hash-seed)')
    after = {name: digest(data) for name, data in inventory().items()}
    need(after == before, 'bound files changed during execution')
    print('PASS: '+str(negative_runs)+' negative-control runs; 4 proof bindings')
    print('RESULT: PASS TR-23 components finite verification')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, TypeError, KeyError, SyntaxError, UnicodeError, RecursionError) as error:
        raise SystemExit('FAIL: verification input: '+type(error).__name__)
