#!/usr/bin/env python3
"""Rebuild every proof module and verify the theorem's kernel dependencies."""

import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
THEOREM = "TR23.finiteCertificate"
EXPECTED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
AXIOMS_SOURCE = (
    "import TR23\n\n"
    "example : TR23.FiniteCertificate := TR23.finiteCertificate\n\n"
    "#print axioms TR23.finiteCertificate\n"
)
# Keep the literal definitions and the complete finite-certificate proposition fixed.
FIXED_SOURCE_HASHES = {'TR23/Statement.lean': '9a93cc03e2ae3c8535c1e8c122daf2540f5be09c31344f3813a6cadd977620d7', 'TR23/GeometryDefinitions.lean': '28e6be327fa61ac6a9039d9f285c32fc62094efdac02c23a366214672ea8d4fe', 'TR23/ExchangeDefinitions.lean': '0e9257d12c0da073204b67e220b89c9948c12ef1925ef4631e5a1e72b501492d', 'TR23/CWDefinitions.lean': 'a346b234052fb28e2719add56ef81875bd020bae7c0700b000776e38303b0208'}
CONFIGURATION_HASHES = {'lakefile.toml': '59a1e2e1c927b1d9be988016c35159c1a39c15bb0498f5b2da5062dd471e1dc0', 'lean-toolchain': '8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88', 'lake-manifest.json': '8fa9ca6d93408b0800085fab07f25b08bd0fd7a7234b587adf7998ceb4665d87', 'certificate/geometry_witness.json': '781d2afb1dd7e62efbf0993a2d3bf4550aae095c4e9d6888155a5295c4278458', 'certificate/certificate.json': 'edf6664a73396a93317cb15330b9ea6be65fee0c63fc2234b182d1519d9e55e4'}
REQUIRED_SOURCES = frozenset(FIXED_SOURCE_HASHES) | {"TR23.lean", "audit/Axioms.lean"}
AUDIT_SOURCES = frozenset({"audit/verify.py", "audit/test_verify.py", "audit/check_literal_data.py"})

MODULE_PATH = re.compile(r"TR23(?:/[A-Za-z][A-Za-z0-9_]*)*\.lean\Z")
# Deliberately include comments, strings, and quoted identifiers in this check.
FORBIDDEN = re.compile(
    r"\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|implemented_by|ofReduceBool|skipKernelTC)\b"
)
AXIOMS_OUTPUT = re.compile(
    r"\s*'TR23\.finiteCertificate' depends on axioms: \[([^\[\]\r\n]*)\]\s*\Z"
)


class AuditError(Exception):
    """A verification condition failed."""


def require(condition, message):
    if not condition:
        raise AuditError(message)


def reject_forbidden(source, name):
    match = FORBIDDEN.search(source)
    require(match is None, f"Disallowed proof token in {name}: "
            f"{match.group(0) if match else ''}")


def check_configuration(root):
    """Bind the build to this source directory and the locked dependencies."""
    snapshot = {}
    for name, expected in CONFIGURATION_HASHES.items():
        path = root / name
        require(path.is_file() and not path.is_symlink(), f"Missing or linked configuration: {name}")
        data = path.read_bytes()
        require(hashlib.sha256(data).hexdigest() == expected, f"Build configuration changed: {name}")
        snapshot[name] = data
    return snapshot


def check_audit_sources(root):
    """Snapshot the audit implementation as well as the checked Lean sources."""
    snapshot = {}
    for name in sorted(AUDIT_SOURCES):
        path = root / name
        require(path.is_file() and not path.is_symlink(), f"Missing or linked audit source: {name}")
        snapshot[name] = path.read_bytes()
    return snapshot


def check_audit_stability(root, before):
    require(check_audit_sources(root) == before, "Audit implementation changed during verification")


def source_paths(root):
    """Enumerate recursively; dependencies are the sole source-tree exclusion."""
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), "Invalid project directory")
    found = []

    def walk_error(error):
        raise AuditError(f"Cannot enumerate project sources: {error}")

    for current, directories, files in os.walk(root, onerror=walk_error, followlinks=False):
        current = Path(current)
        if current == root:
            directories[:] = [name for name in directories if name not in {".lake", ".git"}]
            files = [name for name in files if name != ".git"]
        for name in directories + files:
            path = current / name
            require(not path.is_symlink(), f"Project symlink is not allowed: {path.relative_to(root)}")
        for name in files:
            if name.endswith(".lean"):
                path = current / name
                require(path.is_file(), f"Lean source is not a regular file: {path.relative_to(root)}")
                found.append(path)
    return sorted(found)


def check_sources(root):
    """Check all Lean sources and return their bytes for a later stability check."""
    snapshot = {}
    for path in source_paths(root):
        name = path.relative_to(root).as_posix()
        require(name == "audit/Axioms.lean" or MODULE_PATH.fullmatch(name) is not None,
                f"Unexpected Lean source: {name}")
        data = path.read_bytes()
        try:
            source = data.decode("utf-8")
        except UnicodeDecodeError as error:
            raise AuditError(f"Lean source is not UTF-8: {name}") from error
        reject_forbidden(source, name)
        snapshot[name] = data
    require(REQUIRED_SOURCES <= snapshot.keys(),
            f"Missing required Lean sources: {sorted(REQUIRED_SOURCES - snapshot.keys())}")
    for name, expected in FIXED_SOURCE_HASHES.items():
        actual = hashlib.sha256(snapshot[name]).hexdigest()
        require(actual == expected, f"Fixed theorem source changed: {name}")
    require(snapshot["audit/Axioms.lean"] == AXIOMS_SOURCE.encode("utf-8"),
            "The axiom-printing source changed")
    return snapshot


def parse_axioms(stdout, stderr=""):
    require(not stderr, "Unexpected standard error from the axiom check")
    match = AXIOMS_OUTPUT.fullmatch(stdout)
    require(match is not None, "Missing, malformed, or additional axiom output")
    names = [name.strip() for name in match.group(1).split(",")]
    require(len(names) == len(EXPECTED_AXIOMS) and set(names) == EXPECTED_AXIOMS,
            f"Unexpected axiom list: {names}")
    return frozenset(names)


def module_order(snapshot):
    """Build local dependencies first, one target at a time."""
    sources = {name[:-5].replace("/", "."): data.decode("utf-8")
               for name, data in snapshot.items() if name != "audit/Axioms.lean"}
    visited, visiting, ordered = set(), set(), []

    def visit(module):
        require(module in sources, f"Missing local import: {module}")
        require(module not in visiting, f"Local import cycle: {module}")
        if module in visited:
            return
        visiting.add(module)
        for line in sources[module].splitlines():
            match = re.match(r"\s*(?:(?:public|private)\s+)?import\s+(.+)", line)
            if match:
                for dependency in match.group(1).split("--", 1)[0].split():
                    if dependency == "TR23" or dependency.startswith("TR23."):
                        visit(dependency)
        visiting.remove(module)
        visited.add(module)
        ordered.append(module)

    for module in sorted(sources):
        visit(module)
    return ordered


PYTHON_CHILDREN = {'audit/check_literal_data.py': ['d384aa10730a7ec13220049bf5c5322a3bc24e3393df76684f9877b99419d7b2', '1dff332d53b76a36656d016575da0d8d712fc5dafbb0ca171be57a837c86a766', 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855']}


def run_python_checked(command, root, *args, **kwargs):
    """Authenticate the complete helper program and its expected diagnostics."""
    root = Path(root)
    names = [name for name in PYTHON_CHILDREN
             if name in command or str(root / name) in command]
    require(len(names) == 1, 'Unregistered Python audit child')
    name = names[0]
    path = root / name
    source_hash, stdout_hash, stderr_hash = PYTHON_CHILDREN[name]
    def source():
        require(all(not (root / Path(*Path(name).parts[:i])).is_symlink()
                    for i in range(1, len(Path(name).parts) + 1)),
                'Linked Python audit child: ' + name)
        require(path.is_file(), 'Missing Python audit child: ' + name)
        data = path.read_bytes()
        require(hashlib.sha256(data).hexdigest() == source_hash,
                'Python audit child source mismatch: ' + name)
        return data
    before = source()
    result = run_checked(command, root, *args, **kwargs)
    require(result.returncode == 0, 'Python audit child failed: ' + name)
    stdout, stderr = result.stdout, result.stderr
    if name == 'audit/test_verify.py':
        # unittest's duration is diagnostic; all remaining bytes are bound.
        stderr = re.sub(r'Ran (\d+) tests in [0-9.]+s',
                        r'Ran \1 tests in <time>s', stderr)
    require(hashlib.sha256(stdout.encode('utf-8')).hexdigest() == stdout_hash
            and hashlib.sha256(stderr.encode('utf-8')).hexdigest() == stderr_hash,
            'Python audit child output mismatch: ' + name)
    require(source() == before, 'Python audit child changed during execution: ' + name)
    return result


def run_checked(command, root):
    print("+ " + " ".join(command), flush=True)
    try:
        result = subprocess.run(command, cwd=root, text=True, encoding="utf-8",
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    except (OSError, UnicodeError) as error:
        raise AuditError(f"Could not execute {command[0]}: {error}") from error
    if result.stdout:
        print(result.stdout, end="", flush=True)
    if result.stderr:
        print(result.stderr, end="", file=sys.stderr, flush=True)
    require(result.returncode == 0,
            f"Command failed with status {result.returncode}: {' '.join(command)}")
    return result


def verify(root=ROOT):
    root = Path(root)
    audit_before = check_audit_sources(root)
    configuration_before = check_configuration(root)
    before = check_sources(root)
    run_python_checked([sys.executable, "-B", "audit/check_literal_data.py"], root)
    modules = module_order(before)
    # Naming the package preserves the downloaded dependency cache.
    run_checked(["lake", "clean", "tr23finite"], root)
    for module in modules:
        run_checked(["lake", "build", module], root)
    result = run_checked(["lake", "env", "lean", "audit/Axioms.lean"], root)
    parse_axioms(result.stdout, result.stderr)
    require(check_sources(root) == before, "Lean sources changed during verification")
    require(check_configuration(root) == configuration_before,
            "Build configuration changed during verification")
    run_python_checked([sys.executable, "-B", "audit/check_literal_data.py"], root)
    check_audit_stability(root, audit_before)
    print(f"PASS: rebuilt {len(modules)} proof modules; all project Lean sources checked.")
    print(f"PASS: {THEOREM} uses exactly propext, Classical.choice, Quot.sound.")


def main():
    try:
        verify()
    except (AuditError, OSError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
