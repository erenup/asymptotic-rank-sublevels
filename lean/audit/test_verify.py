#!/usr/bin/env python3
"""Negative controls for source inspection, dependency output, and execution."""

from contextlib import redirect_stderr, redirect_stdout
import io
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest

sys.dont_write_bytecode = True
import verify


VALID_OUTPUT = (
    "'TR23.finiteCertificate' depends on axioms: "
    "[propext, Classical.choice, Quot.sound]\n"
)


class AuditControls(unittest.TestCase):
    def test_valid_sources_and_output(self):
        root = self.fixture()
        (root / "TR23" / "CWIdentity.lean").write_bytes(
            (verify.ROOT / "TR23" / "CWIdentity.lean").read_bytes())
        snapshot = verify.check_sources(root)
        self.assertIn("TR23/CWIdentity.lean", snapshot)
        self.assertEqual(set(verify.check_configuration(root)), set(verify.CONFIGURATION_HASHES))
        self.assertEqual(verify.parse_axioms(VALID_OUTPUT), verify.EXPECTED_AXIOMS)
        self.assertEqual(verify.parse_axioms(VALID_OUTPUT.replace(
            "propext, Classical.choice, Quot.sound", "Quot.sound, propext, Classical.choice")),
            verify.EXPECTED_AXIOMS)

    def test_forbidden_proof_tokens(self):
        for source in (
            "theorem bad : False := by sorry",
            "theorem bad : False := by\n  admit",
            "axiom bad : False", "axiom/- declaration -/bad : False",
            "theorem bad : False := by\n  «sorry»",
            "theorem bad : False := by\n  exact sorryAx _ false",
            "unsafe def bad := 0", "by native_decide",
            "@[implemented_by bad] def safe := 0", "Lean.ofReduceBool",
            "set_option debug.skipKernelTC true",
            '/- sorry -/', 'def text := "admit"',
        ):
            with self.subTest(source=source), self.assertRaises(verify.AuditError):
                verify.reject_forbidden(source, "example.lean")

    def test_missing_extra_and_malformed_axiom_output(self):
        for output in (
            "", "Build completed successfully.\n", VALID_OUTPUT + VALID_OUTPUT,
            "unrelated output\n" + VALID_OUTPUT, VALID_OUTPUT + "extra output\n",
            VALID_OUTPUT.replace("finiteCertificate", "otherTheorem"),
            VALID_OUTPUT.replace("]", ", sorryAx]"),
            VALID_OUTPUT.replace(", Quot.sound", ""),
            VALID_OUTPUT.replace("Quot.sound", "propext"),
            VALID_OUTPUT.replace("]", ", propext]"),
            VALID_OUTPUT.replace("[propext, Classical.choice, Quot.sound]", "[]"),
            VALID_OUTPUT.replace("]", ""),
        ):
            with self.subTest(output=output), self.assertRaises(verify.AuditError):
                verify.parse_axioms(output)
        with self.assertRaises(verify.AuditError):
            verify.parse_axioms(VALID_OUTPUT, "warning: unexpected diagnostic\n")

    def fixture(self):
        temporary_root = verify.ROOT / ".lake"
        temporary_root.mkdir(exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix="audit-control-", dir=temporary_root)
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        for name in verify.REQUIRED_SOURCES | verify.CONFIGURATION_HASHES.keys() | verify.AUDIT_SOURCES:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((verify.ROOT / name).read_bytes())
        return root

    def test_audit_implementation_stability(self):
        for name in verify.AUDIT_SOURCES:
            root = self.fixture()
            before = verify.check_audit_sources(root)
            verify.check_audit_stability(root, before)
            path = root / name
            path.write_bytes(path.read_bytes() + b"\n# altered\n")
            with self.subTest(name=name), self.assertRaises(verify.AuditError):
                verify.check_audit_stability(root, before)
            path.unlink()
            with self.assertRaises(verify.AuditError):
                verify.check_audit_sources(root)
            path.symlink_to(verify.ROOT / name)
            with self.assertRaises(verify.AuditError):
                verify.check_audit_sources(root)

    def test_configuration_cannot_redirect_the_build(self):
        replacements = {
            "lakefile.toml": 'name = "tr23finite"\n[[lean_lib]]\nname = "TR23"\nsrcDir = "shadow"\n',
            "lean-toolchain": "leanprover/lean4:nightly\n",
            "lake-manifest.json": '{"packages": []}\n',
            "certificate/geometry_witness.json": '{"permutation_tensor": []}\n',
            "certificate/certificate.json": '{"source_terms_scaled": []}\n',
        }
        for name, replacement in replacements.items():
            root = self.fixture()
            (root / name).write_text(replacement, encoding="utf-8")
            with self.subTest(name=name), self.assertRaises(verify.AuditError):
                verify.check_configuration(root)

    def test_missing_or_linked_configuration(self):
        for name in verify.CONFIGURATION_HASHES:
            root = self.fixture()
            path = root / name
            path.unlink()
            with self.subTest(name=name, linked=False), self.assertRaises(verify.AuditError):
                verify.check_configuration(root)
            path.symlink_to(verify.ROOT / name)
            with self.subTest(name=name, linked=True), self.assertRaises(verify.AuditError):
                verify.check_configuration(root)

    def test_nested_sources_and_dependency_exclusion(self):
        root = self.fixture()
        nested = root / "TR23" / "Nested" / "Bad.lean"
        nested.parent.mkdir()
        nested.write_text("theorem bad : False := by sorry\n", encoding="utf-8")
        with self.assertRaises(verify.AuditError):
            verify.check_sources(root)
        nested.write_text("theorem good : True := by trivial\n", encoding="utf-8")
        dependency = root / ".lake" / "packages" / "Dependency.lean"
        dependency.parent.mkdir(parents=True)
        dependency.write_text("axiom dependency : False\n", encoding="utf-8")
        self.assertIn("TR23/Nested/Bad.lean", verify.check_sources(root))
        self.assertNotIn(".lake/packages/Dependency.lean", verify.check_sources(root))

    def test_fixed_sources_cannot_be_spoofed_by_comments(self):
        for name in verify.FIXED_SOURCE_HASHES:
            root = self.fixture()
            path = root / name
            path.write_text("/-\n" + path.read_text(encoding="utf-8") + "\n-/\n",
                            encoding="utf-8")
            with self.subTest(name=name), self.assertRaises(verify.AuditError):
                verify.check_sources(root)

    def test_required_file_missing(self):
        for name in verify.REQUIRED_SOURCES:
            root = self.fixture()
            (root / name).unlink()
            with self.subTest(name=name), self.assertRaises(verify.AuditError):
                verify.check_sources(root)

    def test_forged_axiom_probe(self):
        root = self.fixture()
        (root / "audit" / "Axioms.lean").write_text(
            '#eval IO.println "' + VALID_OUTPUT.strip() + '"\n', encoding="utf-8")
        with self.assertRaises(verify.AuditError):
            verify.check_sources(root)

    def test_unexpected_lean_file(self):
        root = self.fixture()
        (root / "Unbuilt.lean").write_text("theorem unused : True := by trivial\n", encoding="utf-8")
        with self.assertRaises(verify.AuditError):
            verify.check_sources(root)

    def test_symlink_file_and_directory(self):
        for directory in (False, True):
            root = self.fixture()
            target = root / "TR23" if directory else root / "TR23.lean"
            link = root / ("Linked" if directory else "Linked.lean")
            link.symlink_to(target, target_is_directory=directory)
            with self.subTest(directory=directory), self.assertRaises(verify.AuditError):
                verify.check_sources(root)

    def test_execution_failure_cannot_be_hidden_by_valid_output(self):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            with self.assertRaises(verify.AuditError):
                verify.run_checked([sys.executable, "-c",
                                    f"print({VALID_OUTPUT!r}); raise SystemExit(7)"], verify.ROOT)
            with self.assertRaises(verify.AuditError):
                verify.run_checked(["./missing-audit-command"], verify.ROOT)
            result = verify.run_checked([sys.executable, "-c", f"print({VALID_OUTPUT!r})"], verify.ROOT)
        self.assertEqual(verify.parse_axioms(result.stdout), verify.EXPECTED_AXIOMS)

    def test_all_modules_built_after_local_dependencies(self):
        sources = {
            "TR23.lean": b"import TR23.C\n",
            "TR23/A.lean": b"import TR23.B\n",
            "TR23/B.lean": b"import Mathlib\n",
            "TR23/C.lean": b"import TR23.A TR23.B -- prerequisites\n",
            "TR23/Unimported.lean": b"import TR23.B\n",
            "audit/Axioms.lean": verify.AXIOMS_SOURCE.encode(),
        }
        ordered = verify.module_order(sources)
        self.assertEqual(set(ordered), {"TR23", "TR23.A", "TR23.B", "TR23.C", "TR23.Unimported"})
        self.assertEqual(len(ordered), 5)
        for earlier, later in [("TR23.B", "TR23.A"), ("TR23.A", "TR23.C"),
                               ("TR23.C", "TR23"), ("TR23.B", "TR23.Unimported")]:
            self.assertLess(ordered.index(earlier), ordered.index(later))

    def test_literal_data_controls(self):
        command = [sys.executable, '-B']
        if sys.flags.optimize:
            command.append('-O')
        command.append(str(verify.ROOT / 'audit' / 'check_literal_data.py'))
        positive = subprocess.run(command, capture_output=True, cwd=verify.ROOT)
        self.assertEqual(positive.returncode, 0)
        self.assertEqual(positive.stderr, b'')
        self.assertEqual(positive.stdout,
            b'PASS: geometry literals, 126 minor rows, exchange map and tight weights\n')
        for control, error in (
            ('--wrong-geometry', b'FAIL: permutation tensor\n'),
            ('--wrong-exchange', b'FAIL: exchange row matrix\n'),
        ):
            with self.subTest(control=control):
                result = subprocess.run(command + [control], capture_output=True, cwd=verify.ROOT)
                self.assertEqual(result.returncode, 1)
                self.assertEqual(result.stdout, b'')
                self.assertEqual(result.stderr, error)

    def test_missing_imports_and_cycles_rejected(self):
        for sources in (
            {"TR23.lean": b"import TR23.Missing\n"},
            {"TR23.lean": b"import TR23.A\n", "TR23/A.lean": b"import TR23\n"},
        ):
            with self.subTest(sources=sources), self.assertRaises(verify.AuditError):
                verify.module_order(sources)


if __name__ == "__main__":
    unittest.main()
