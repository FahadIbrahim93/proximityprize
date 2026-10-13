"""The prize audit must find its predicate in the result, not just an assumption."""
import contextlib
import io
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import proximity_prize_cleanroom_audit as audit


def entry(name="candidate"):
    return audit.Entry("active", "Init", name, "mcaPrize", (), 1)


def output(signature, name="candidate"):
    return f"{name} {signature}\n'{name}' does not depend on any axioms\n"


class ConclusionBoundaryTests(unittest.TestCase):
    def test_binder_only_predicate_is_rejected(self):
        self.assertTrue(audit.check_signature(entry(), output("(h : mcaPrize n) : True")))

    def test_arrow_only_predicate_is_rejected(self):
        for result in ("mcaPrize n → True", "(mcaPrize n → True)",
                       "Nat → (mcaPrize n → True)"):
            with self.subTest(result=result):
                self.assertTrue(audit.check_signature(entry(), output(": " + result)))

    def test_goal_equivalent_premises_remain_rejected(self):
        for signature in ("(h : mcaPrize n) : mcaPrize n",
                          ": mcaPrize n → mcaPrize n"):
            with self.subTest(signature=signature):
                errors = audit.check_signature(entry(), output(signature))
                self.assertTrue(any("appears in hypotheses" in e for e in errors))

    def test_real_result_and_conjunction_are_accepted(self):
        for signature in (": mcaPrize 0", "(n : Nat) : mcaPrize n ∧ True",
                          ": ¬ mcaPrize n", ": ∀ n, mcaPrize n",
                          ": Nat → ((mcaPrize 0))"):
            with self.subTest(signature=signature):
                self.assertEqual(audit.check_signature(entry(), output(signature)), [])

    def test_arrows_in_binders_and_result_arguments_are_not_premises(self):
        for signature in ("(f : Nat → Nat) : mcaPrize (f 0)",
                          ": mcaPrize (fun (f : Nat → Nat) => f 0)"):
            with self.subTest(signature=signature):
                self.assertEqual(audit.check_signature(entry(), output(signature)), [])

    def test_residual_and_extra_forbidden_premises_remain_rejected(self):
        self.assertTrue(audit.check_signature(entry(), output("(h : CoreResidual) : mcaPrize 0")))
        self.assertTrue(audit.check_signature(entry(), output(": ∀ (h : CoreResidual), mcaPrize 0")))
        target = audit.Entry("active", "Init", "candidate", "mcaPrize", ("CoreInput",), 1)
        self.assertTrue(audit.check_signature(target, output(": CoreInput → mcaPrize 0")))

    def test_longer_identifier_is_not_the_expected_predicate(self):
        self.assertTrue(audit.check_signature(entry(), output(": mcaPrizePlaceholder")))
        self.assertEqual(audit.check_signature(entry(), output(": Namespace.mcaPrize 0")), [])

    def test_multiline_printed_signature(self):
        self.assertTrue(audit.check_signature(entry(), output("(n : Nat)\n  (h : mcaPrize n) :\n  True")))


class LeanReproductionTests(unittest.TestCase):
    def test_real_lean_output_fails_the_cli_audit(self):
        lean = os.environ.get("LEAN_TEST_EXECUTABLE") or shutil.which("lean")
        if not lean:
            self.skipTest("Lean is required for the independent printed-signature reproduction")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Probe.lean"
            source.write_text(
                "def mcaPrize (n : Nat) : Prop := n = 0\n"
                "theorem candidate (n : Nat) (h : mcaPrize n) : True := trivial\n"
                "#check candidate\n#print axioms candidate\n", encoding="utf-8")
            proc = subprocess.run([lean, str(source)], capture_output=True,
                                  text=True, encoding="utf-8", timeout=60)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
            self.assertEqual(audit.parse_axioms(proc.stdout)["candidate"], set())
            manifest = root / "targets.txt"
            manifest.write_text("active Init candidate mcaPrize\n", encoding="utf-8")
            with patch.object(sys, "argv", ["audit", "--manifest", str(manifest)]), \
                    patch.object(audit, "run_lean", return_value=(0, proc.stdout)), \
                    contextlib.redirect_stderr(io.StringIO()) as errors:
                self.assertEqual(audit.main(), 1)
            self.assertIn("conclusion token", errors.getvalue())


class ManifestModuleTests(unittest.TestCase):
    def test_default_manifest_imports_exist(self):
        self.assertEqual(audit.missing_local_modules(audit.parse_manifest(audit.DEFAULT_MANIFEST)), [])

    def test_missing_active_module_is_rejected_and_pending_is_allowed(self):
        with tempfile.TemporaryDirectory() as directory:
            active = audit.Entry("active", "Research.ProximityPrize.Missing", "candidate", "mcaPrize", (), 1)
            pending = audit.Entry("pending", "Research.ProximityPrize.Future", "future", "mcaPrize", (), 2)
            failures = audit.missing_local_modules([active, pending], Path(directory))
            self.assertEqual(len(failures), 1)
            self.assertIn(active.module, failures[0])
            source = Path(directory) / "Research/ProximityPrize/Missing.lean"
            source.parent.mkdir(parents=True)
            source.write_text("", encoding="utf-8")
            self.assertEqual(audit.missing_local_modules([active, pending], Path(directory)), [])


if __name__ == "__main__":
    unittest.main()
