"""Adversarial stdlib tests for saved diagnostic evidence validation.

Fixtures copy the project's actual JSON inputs and certificate sources into a
temporary directory. These tests exercise the Python checks and Lean-audit
plumbing; the project verifier separately compiles the generated Lean source.
Run with ``python scripts/test_verify_evidence.py``. The suite also runs itself
under ``python -O`` so disabling Python assertions cannot bypass rejection.
Set ``GROWTH_TEST_LEAN=1`` and ``GROWTH_LAKE`` to an absolute Lake executable
path to include the real Lean rejection test, using this project's toolchain
and already installed dependencies.
"""
from copy import deepcopy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import check_theorydebugger
import verify
import verify_evidence as evidence


PROJECT = Path(__file__).resolve().parents[1]


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="growth-evidence-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.td = self.root / "verification/theorydebugger"
        self.td.mkdir(parents=True)
        self.cases = deepcopy(check_theorydebugger.cases())
        self.environment = json.loads(
            (PROJECT / "verification/theorydebugger/environment.json").read_text(encoding="utf-8"))
        self.results = json.loads(
            (PROJECT / "verification/theorydebugger/results.json").read_text(encoding="utf-8"))
        files = ["scripts/check_theorydebugger.py", "lake-manifest.json"]
        files += ["verification/theorydebugger/inputs/" + name + ".json"
                  for name, _, _ in self.cases]
        files += [certificate["source"] for result in self.results
                  for certificate in result["certificates"]]
        for relative in files:
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(PROJECT / relative, target)
        self.save_metadata()

    def save_metadata(self):
        self.write_json(self.td / "environment.json", self.environment)
        self.write_json(self.td / "results.json", self.results)

    @staticmethod
    def write_json(path, value):
        path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")

    def prepare(self):
        self.save_metadata()
        return evidence.prepare(self.root, self.cases, verify.uncomment)

    def reject(self, message):
        with self.assertRaisesRegex(RuntimeError, message):
            self.prepare()

    def first_input(self):
        return self.td / "inputs" / (self.cases[0][0] + ".json")

    def first_certificate(self):
        return self.results[0]["certificates"][0]

    def change_certificate_source(self, text):
        certificate = self.first_certificate()
        path = self.root / certificate["source"]
        path.write_text(text, encoding="utf-8")
        certificate["source_sha256"] = evidence.digest(path)

    def test_untouched_real_evidence_is_accepted(self):
        fresh, declarations, count, certificate_count = self.prepare()
        self.assertEqual(count, len(self.cases))
        self.assertEqual(certificate_count, sum(len(r["certificates"]) for r in self.results))
        self.assertEqual(len(declarations), len(set(declarations)))
        self.assertGreaterEqual(len(declarations), certificate_count)
        self.assertIn("theorem checkedClaim", fresh)
        self.assertIn("theorem checkedFeasible", fresh)
        self.assertIn("TheoryDebugger.Generated.original =", fresh)
        self.assertNotIn("import Solow1956", fresh)
        self.assertNotIn("import RamseyCassKoopmans", fresh)

    def test_changed_input_is_rejected(self):
        self.first_input().write_text("{}\n", encoding="utf-8")
        self.reject("Input hash mismatch")

    def test_changed_input_with_replaced_hash_is_still_rejected(self):
        path = self.first_input()
        saved = json.loads(path.read_text(encoding="utf-8"))
        saved["goal"] = ["not", saved["goal"]]
        self.write_json(path, saved)
        self.environment["input_sha256"][path.name] = evidence.digest(path)
        self.reject("Input differs from declared case")

    def test_changed_declared_case_is_rejected(self):
        self.cases[0][2]["goal"] = False
        self.reject("Input differs from declared case")

    def test_missing_input_is_rejected(self):
        self.first_input().unlink()
        self.reject("Diagnostic input inventory mismatch")

    def test_additional_input_is_rejected(self):
        self.write_json(self.td / "inputs/unexpected.json", {})
        self.reject("Diagnostic input inventory mismatch")

    def test_missing_input_hash_is_rejected(self):
        self.environment["input_sha256"].pop(self.first_input().name)
        self.reject("Diagnostic input inventory mismatch")

    def test_missing_result_is_rejected(self):
        self.results.pop()
        self.reject("Missing, reordered, or duplicate diagnostic results")

    def test_reordered_results_are_rejected(self):
        self.results[0], self.results[1] = self.results[1], self.results[0]
        self.reject("Missing, reordered, or duplicate diagnostic results")

    def test_duplicate_result_is_rejected(self):
        self.results.append(deepcopy(self.results[0]))
        self.reject("Missing, reordered, or duplicate diagnostic results")

    def test_duplicate_declared_case_is_rejected(self):
        self.cases.append(deepcopy(self.cases[0]))
        self.reject("Duplicate diagnostic cases")

    def test_changed_result_problem_is_rejected(self):
        self.results[0]["problem"]["goal"] = False
        self.reject("Result belongs to another problem")

    def test_changed_problem_identity_is_rejected(self):
        self.results[0]["problem_sha256"] = "0" * 64
        self.reject("Problem identity mismatch")

    def test_counterfeit_validity_evidence_is_rejected(self):
        self.results[0]["validity"]["evidence"] = "solver"
        self.reject("Unexpected validity")

    def test_counterfeit_validity_status_is_rejected(self):
        self.results[0]["validity"]["status"] = "unknown"
        self.reject("Unexpected validity")

    def test_counterfeit_consistency_is_rejected(self):
        self.results[0]["consistency"]["status"] = "inconsistent"
        self.reject("Incomplete diagnostic")

    def test_diagnostic_warnings_are_rejected(self):
        self.results[0]["warnings"] = ["certificate was not checked"]
        self.reject("Incomplete diagnostic")

    def test_missing_certificate_is_rejected(self):
        self.results[0]["certificates"].pop()
        self.reject("Missing claim or feasibility certificate")

    def test_duplicate_certificate_kind_is_rejected(self):
        certificates = self.results[0]["certificates"]
        certificates[1]["kind"] = certificates[0]["kind"]
        self.reject("Missing claim or feasibility certificate")

    def test_counterfeit_certificate_status_is_rejected(self):
        self.first_certificate()["status"] = "not_checked"
        self.reject("Saved certificate did not succeed")

    def test_unsuccessful_compilation_is_rejected(self):
        self.first_certificate()["compiler_exit_code"] = 1
        self.reject("Saved certificate did not succeed")

    def test_counterfeit_formal_goal_is_rejected(self):
        self.first_certificate()["formal_goal"] = "True"
        self.reject("Certificate metadata has another goal")

    def test_changed_certificate_hash_is_rejected(self):
        self.first_certificate()["source_sha256"] = "0" * 64
        self.reject("Certificate hash mismatch")

    def test_changed_certificate_file_is_rejected(self):
        path = self.root / self.first_certificate()["source"]
        path.write_text(path.read_text(encoding="utf-8") + "\n-- changed\n", encoding="utf-8")
        self.reject("Certificate hash mismatch")

    def test_wrong_certificate_source_is_rejected(self):
        certificate = self.first_certificate()
        other = next(c for r in self.results for c in r["certificates"]
                     if c["source_sha256"] != certificate["source_sha256"])
        certificate["source"] = other["source"]
        self.reject("Certificate hash mismatch")

    def test_relative_certificate_escape_is_rejected(self):
        certificate = self.first_certificate()
        outside = self.td / "outside.lean"
        shutil.copyfile(self.root / certificate["source"], outside)
        certificate["source"] = "verification/theorydebugger/certificates/../outside.lean"
        self.reject("Certificate outside evidence directory")

    def test_absolute_certificate_escape_is_rejected(self):
        certificate = self.first_certificate()
        outside = self.root / "outside.lean"
        shutil.copyfile(self.root / certificate["source"], outside)
        certificate["source"] = str(outside.resolve())
        self.reject("Certificate outside evidence directory")

    def test_unchecked_source_with_replaced_hash_is_rejected(self):
        path = self.root / self.first_certificate()["source"]
        self.change_certificate_source(path.read_text(encoding="utf-8") + "\naxiom injected : False\n")
        self.reject("Unchecked certificate source")

    def test_local_import_with_replaced_hash_is_rejected(self):
        path = self.root / self.first_certificate()["source"]
        self.change_certificate_source("import Untrusted.LocalProof\n" + path.read_text(encoding="utf-8"))
        self.reject("Certificate imports a local proof")

    def test_changed_diagnostic_script_is_rejected(self):
        (self.root / "scripts/check_theorydebugger.py").write_text("# changed\n", encoding="utf-8")
        self.reject("Diagnostic script hash mismatch")

    def test_changed_mathlib_manifest_is_rejected(self):
        (self.root / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
        self.reject("Diagnostic Mathlib hash mismatch")

    def test_changed_case_count_is_rejected(self):
        self.environment["cases"] += 1
        self.reject("Evidence counts mismatch")

    def test_changed_certificate_count_is_rejected(self):
        self.environment["certificates"] += 1
        self.reject("Evidence counts mismatch")

    def test_failed_fresh_compilation_propagates(self):
        self.prepare()
        calls = []

        def failed_compile(path):
            calls.append(path)
            self.assertTrue(path.is_file())
            raise RuntimeError("fresh Lean compilation failed")

        with self.assertRaisesRegex(RuntimeError, "fresh Lean compilation failed"):
            evidence.verify(self.root, self.cases, verify.uncomment, failed_compile)
        self.assertEqual(len(calls), 1)

    def test_saved_success_cannot_replace_missing_fresh_axiom_audit(self):
        self.prepare()
        with self.assertRaisesRegex(RuntimeError, "Missing axiom audit"):
            evidence.verify(self.root, self.cases, verify.uncomment, lambda _: "")

    def test_saved_success_cannot_authorize_extra_fresh_axioms(self):
        _, declarations, _, _ = self.prepare()
        log = "\n".join("'" + name + "' depends on axioms: [sorryAx]" for name in declarations)
        with self.assertRaisesRegex(RuntimeError, "Unapproved axioms"):
            evidence.verify(self.root, self.cases, verify.uncomment, lambda _: log)

    @unittest.skipUnless(os.environ.get("GROWTH_TEST_LEAN") == "1", "real Lean test is opt-in")
    def test_real_lean_rejects_unrelated_proof_despite_success_metadata(self):
        configured_lake = os.environ.get("GROWTH_LAKE")
        self.assertTrue(configured_lake, "GROWTH_LAKE must specify an absolute Lake executable path")
        lake = Path(configured_lake)
        self.assertTrue(lake.is_absolute() and lake.is_file(), "GROWTH_LAKE must identify a real executable")

        certificate = next(c for r in self.results for c in r["certificates"] if c["kind"] == "valid")
        path = self.root / certificate["source"]
        source = path.read_text(encoding="utf-8")
        start = source.index("\ntheorem claim : original := by\n")
        end = source.index("\n#check claim", start)
        tampered = source[:start] + "\ntheorem claim : True := by\n  trivial\n" + source[end:]
        path.write_text(tampered, encoding="utf-8")
        certificate["source_sha256"] = evidence.digest(path)

        # The original proposition, formal_goal, and all success metadata are
        # retained. Hash/schema checks alone should accept this forged evidence.
        fresh, _, _, _ = self.prepare()
        fresh_path = self.root / "verification/TamperedCertificates.lean"
        fresh_path.write_text(fresh, encoding="utf-8")
        result = subprocess.run(
            [str(lake), "env", "lean", str(fresh_path)], cwd=PROJECT,
            capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=180)
        log = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, "Lean accepted the unrelated True proof")
        self.assertIn("type mismatch", log.lower(), log)
        self.assertIn("TheoryDebugger.Generated.claim", log, log)

    @unittest.skipIf(sys.flags.optimize, "already running with Python optimization")
    def test_all_rejections_survive_python_optimization(self):
        # The optimized subprocess repeats Python validation; compile the
        # opt-in Lean boundary test only once in the outer suite.
        child_environment = os.environ.copy()
        child_environment.pop("GROWTH_TEST_LEAN", None)
        result = subprocess.run(
            [sys.executable, "-O", str(Path(__file__).resolve())],
            cwd=PROJECT, env=child_environment, capture_output=True, text=True,
            encoding="utf-8", timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
