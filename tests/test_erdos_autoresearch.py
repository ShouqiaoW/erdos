from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
import zipfile
from datetime import datetime, timedelta, timezone
from pathlib import Path


REPOSITORY = Path(__file__).resolve().parents[1]
SKILL = REPOSITORY / "skills" / "erdos-autoresearch"
SCRIPTS = SKILL / "scripts"
AUDIT_LANES = [
    "statement",
    "quantifier",
    "edge_case",
    "dependency",
    "external_theorem",
    "counterexample",
    "computation",
    "formalization",
    "clean_room",
    "reproduction",
    "prior_art",
]
OPENAI_PROMPT_SHA256 = (
    "4d7276c0f39937589f8d0e90a32330219ff9462e5de98bacbd5af31d664cad48"
)


def run_script(
    name: str,
    *args: str,
    check: bool = True,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPTS / name), *args],
        text=True,
        capture_output=True,
        check=check,
        env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
    )


def write_json(path: Path, value: object) -> None:
    path.write_text(
        json.dumps(value, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


class SyntheticCase:
    def __init__(self, root: Path, case_id: str = "synthetic") -> None:
        self.root = root
        self.case_id = case_id
        self.base = root / "cases"
        self.case = self.base / case_id
        self.problem = root / f"{case_id}-problem.md"
        self.problem.write_text(
            "# Exact problem\n\n"
            "Prove that every object in the source-defined class C has property P.\n",
            encoding="utf-8",
        )

    def initialize(self) -> None:
        run_script(
            "init_case.py",
            "--case-id",
            self.case_id,
            "--title",
            "Synthetic theorem",
            "--problem-file",
            str(self.problem),
            "--base",
            str(self.base),
        )
        run_script(
            "freeze_statement.py",
            "--case",
            str(self.case),
            "--input",
            str(self.problem),
            "--source-uri",
            "local:synthetic-test",
        )
        contract_path = self.case / "contract" / "problem_contract.json"
        contract = json.loads(contract_path.read_text(encoding="utf-8"))
        affirmative = "For every object x in C, property P(x) holds."
        contract["canonical_statement"] = affirmative
        contract["definitions"] = [
            {
                "id": "DEF-0001",
                "term": "C",
                "definition": "The exact class specified by the frozen source.",
            },
            {
                "id": "DEF-0002",
                "term": "P",
                "definition": "The exact property specified by the frozen source.",
            },
        ]
        contract["quantifier_matrix"] = [
            {
                "id": "QNT-0001",
                "variable": "x",
                "domain": "C",
                "quantifier": "forall",
                "order": 1,
                "depends_on": [],
                "must_be_uniform_in": [],
            }
        ]
        contract["allowed_outcomes"]["affirmative"] = {
            "enabled": True,
            "statement": affirmative,
            "obligations": ["Prove P(x) for an arbitrary x in C."],
        }
        contract["non_solutions"] = [
            "Finite verification only.",
            "A proof for a strict subclass.",
            "A reduction to an unproved equivalent statement.",
        ]
        contract["traps"] = [
            {
                "id": "TRAP-0001",
                "description": "Restricting to a strict subclass.",
                "regression_test": "Check arbitrary x in C.",
            },
            {
                "id": "TRAP-0002",
                "description": "Treating finite evidence as universal proof.",
                "regression_test": "Locate the exhaustive argument.",
            },
            {
                "id": "TRAP-0003",
                "description": "Circular theorem-strength reduction.",
                "regression_test": "Audit dependency strength.",
            },
        ]
        contract["edge_cases"] = ["Every degenerate object admitted by the source."]
        contract["semantic_audits"] = [
            {"auditor": "statement-auditor-a", "status": "pass", "findings": []},
            {"auditor": "statement-auditor-b", "status": "pass", "findings": []},
        ]
        write_json(contract_path, contract)
        run_script("validate_contract.py", "--case", str(self.case))
        run_script("compile_research_prompt.py", "--case", str(self.case))

    def add_claim_graph(self) -> tuple[str, str]:
        route = run_script(
            "add_route.py",
            "--case",
            str(self.case),
            "--family",
            "direct",
            "--mechanism",
            "Derive P directly from the frozen definitions.",
            "--status",
            "active",
        ).stdout.strip()

        lemma_proof = self.case / "claims" / "lemma-proof.md"
        lemma_proof.write_text("Complete proof of the supporting lemma.\n", encoding="utf-8")
        lemma = run_script(
            "add_claim.py",
            "--case",
            str(self.case),
            "--statement",
            "The supporting lemma holds.",
            "--status",
            "proved",
            "--route-id",
            route,
            "--proof-location",
            "claims/lemma-proof.md",
        ).stdout.strip()

        final_proof = self.case / "claims" / "final-proof.md"
        final_proof.write_text(
            "Complete proof of the exact affirmative outcome.\n",
            encoding="utf-8",
        )
        final_claim = run_script(
            "add_claim.py",
            "--case",
            str(self.case),
            "--affirmative-outcome",
            "--status",
            "proved",
            "--route-id",
            route,
            "--dependencies",
            lemma,
            "--proof-location",
            "claims/final-proof.md",
        ).stdout.strip()
        run_script(
            "validate_claim_graph.py",
            "--case",
            str(self.case),
            "--final-claim",
            final_claim,
        )
        return lemma, final_claim

    def freeze(self, final_claim: str, *, force: bool = False) -> None:
        candidate = self.case / "scratch" / "candidate.tex"
        candidate.write_text(
            "\\documentclass{article}\n"
            "\\begin{document}\n"
            "Complete synthetic candidate.\n"
            "\\end{document}\n",
            encoding="utf-8",
        )
        arguments = [
            "--case",
            str(self.case),
            "--proof-source",
            str(candidate),
            "--final-claim",
            final_claim,
            "--candidate-kind",
            "affirmative",
        ]
        if force:
            arguments.append("--force")
        run_script("freeze_candidate.py", *arguments)

    def prepare_release_artifacts(self) -> None:
        (self.case / "audit" / "audit_report.md").write_text(
            "# Audit report\n\nEvery required lane is reported separately.\n",
            encoding="utf-8",
        )
        (self.case / "audit" / "prior_art_report.md").write_text(
            "# Prior-art report\n\nSynthetic test; no novelty claim.\n",
            encoding="utf-8",
        )
        (self.case / "release" / "README.md").write_text(
            "# Candidate package\n\n"
            "Status: `INTERNALLY_AUDITED_CANDIDATE`. "
            "No external acceptance is claimed.\n",
            encoding="utf-8",
        )

    def record_all_audits(self) -> None:
        for lane in AUDIT_LANES:
            if lane == "prior_art":
                report = self.case / "audit" / "prior_art_report.md"
            else:
                report = self.case / "audit" / f"{lane}-report.md"
                report.write_text(
                    f"# {lane} audit\n\nSynthetic independent pass.\n",
                    encoding="utf-8",
                )
            run_script(
                "record_audit.py",
                "--case",
                str(self.case),
                "--lane",
                lane,
                "--auditor",
                f"independent-{lane}-auditor",
                "--status",
                "pass",
                "--report-path",
                str(report.relative_to(self.case)),
                "--independent",
            )

    def backdate(self, hours: float = 9) -> None:
        config_path = self.case / "run_config.json"
        config = json.loads(config_path.read_text(encoding="utf-8"))
        config["created_at"] = (
            datetime.now(timezone.utc) - timedelta(hours=hours)
        ).replace(microsecond=0).isoformat().replace("+00:00", "Z")
        write_json(config_path, config)

    def complete(self, *, backdate: bool = True) -> str:
        self.initialize()
        _, final_claim = self.add_claim_graph()
        if backdate:
            self.backdate()
        self.freeze(final_claim)
        self.prepare_release_artifacts()
        self.record_all_audits()
        return final_claim


class SkillStaticTests(unittest.TestCase):
    def test_every_cli_entry_point_has_help(self) -> None:
        scripts = sorted(
            path.name for path in SCRIPTS.glob("*.py") if path.name != "_common.py"
        )
        self.assertGreaterEqual(len(scripts), 20)
        for script in scripts:
            with self.subTest(script=script):
                result = run_script(script, "--help", check=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("usage:", result.stdout.lower())

    def test_skill_doctor_is_side_effect_free(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            copied_skill = Path(temporary) / "erdos-autoresearch"
            shutil.copytree(SKILL, copied_skill, ignore=shutil.ignore_patterns("__pycache__"))
            result = run_script(
                "skill_doctor.py",
                "--skill-dir",
                str(copied_skill),
            )
            self.assertIn("passed", result.stdout.lower())
            self.assertEqual(list(copied_skill.rglob("__pycache__")), [])

    def test_all_json_assets_and_schemas_parse(self) -> None:
        paths = sorted((SKILL / "assets").glob("*.json"))
        paths += sorted((SKILL / "references" / "schemas").glob("*.json"))
        self.assertGreaterEqual(len(paths), 18)
        for path in paths:
            with self.subTest(path=path.name):
                self.assertIsNotNone(json.loads(path.read_text(encoding="utf-8")))

    def test_openai_example_prompt_is_preserved(self) -> None:
        prompt = SKILL / "references" / "openai-cdc-example-prompt.txt"
        digest = hashlib.sha256(prompt.read_bytes()).hexdigest()
        self.assertEqual(digest, OPENAI_PROMPT_SHA256)


class SkillLifecycleTests(unittest.TestCase):
    def test_minimum_duration_cannot_be_configured_below_eight_hours(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            result = run_script(
                "init_case.py",
                "--case-id",
                "too-short",
                "--title",
                "Too short",
                "--base",
                temporary,
                "--minimum-research-hours",
                "7.99",
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("at least 8", result.stderr)

    def test_intermediate_claim_cannot_be_frozen_as_final(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            synthetic = SyntheticCase(Path(temporary))
            synthetic.initialize()
            lemma, _ = synthetic.add_claim_graph()
            candidate = synthetic.case / "scratch" / "candidate.tex"
            candidate.write_text("candidate\n", encoding="utf-8")
            result = run_script(
                "freeze_candidate.py",
                "--case",
                str(synthetic.case),
                "--proof-source",
                str(candidate),
                "--final-claim",
                lemma,
                "--candidate-kind",
                "affirmative",
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("not role final_affirmative", result.stderr)

    def test_evidence_path_may_not_escape_the_case(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            synthetic = SyntheticCase(root)
            synthetic.initialize()
            outside = root / "outside-proof.md"
            outside.write_text("outside\n", encoding="utf-8")
            result = run_script(
                "add_claim.py",
                "--case",
                str(synthetic.case),
                "--statement",
                "Improper claim.",
                "--status",
                "proved",
                "--proof-location",
                str(outside),
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("escapes case directory", result.stderr)

    def test_missing_external_theorem_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            synthetic = SyntheticCase(Path(temporary))
            synthetic.initialize()
            proof = synthetic.case / "claims" / "external-proof.md"
            proof.write_text("proof\n", encoding="utf-8")
            claim = run_script(
                "add_claim.py",
                "--case",
                str(synthetic.case),
                "--statement",
                "Claim using an undeclared theorem.",
                "--status",
                "proved",
                "--proof-location",
                "claims/external-proof.md",
                "--external-dependencies",
                "EXT-9999",
            ).stdout.strip()
            result = run_script(
                "validate_claim_graph.py",
                "--case",
                str(synthetic.case),
                "--final-claim",
                claim,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("missing external theorem EXT-9999", result.stdout)

    def test_verified_external_theorem_closes_dependency(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            synthetic = SyntheticCase(Path(temporary))
            synthetic.initialize()
            evidence = synthetic.case / "claims" / "external-mapping.md"
            evidence.write_text(
                "Exact source theorem and hypothesis mapping.\n",
                encoding="utf-8",
            )
            theorem = run_script(
                "add_external_theorem.py",
                "--case",
                str(synthetic.case),
                "--statement",
                "If H holds, then Q holds.",
                "--source-uri",
                "https://example.test/theorem",
                "--hypothesis",
                "H holds for the present object.",
                "--application",
                "Contract definition DEF-0001 supplies H.",
                "--evidence-path",
                "claims/external-mapping.md",
                "--status",
                "verified",
            ).stdout.strip()
            proof = synthetic.case / "claims" / "external-proof.md"
            proof.write_text("Complete application.\n", encoding="utf-8")
            run_script(
                "add_claim.py",
                "--case",
                str(synthetic.case),
                "--statement",
                "Q holds.",
                "--status",
                "proved",
                "--proof-location",
                "claims/external-proof.md",
                "--external-dependencies",
                theorem,
            )
            result = run_script(
                "validate_claim_graph.py",
                "--case",
                str(synthetic.case),
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_release_rejects_early_run(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            synthetic = SyntheticCase(Path(temporary))
            final_claim = synthetic.complete(backdate=False)
            result = run_script(
                "release_gate.py",
                "--case",
                str(synthetic.case),
                "--status",
                "INTERNALLY_AUDITED_CANDIDATE",
                "--final-claim",
                final_claim,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Minimum research duration not met", result.stdout)

    def test_partial_status_is_not_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            synthetic = SyntheticCase(Path(temporary))
            synthetic.initialize()
            result = run_script(
                "release_gate.py",
                "--case",
                str(synthetic.case),
                "--status",
                "PARTIAL_THEOREM",
                "--final-claim",
                "CLM-0001",
                check=False,
            )
            self.assertEqual(result.returncode, 2)
            self.assertIn("invalid choice", result.stderr)

    def test_missing_current_generation_audits_block_release(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            synthetic = SyntheticCase(Path(temporary))
            final_claim = synthetic.complete()
            synthetic.freeze(final_claim, force=True)
            result = run_script(
                "release_gate.py",
                "--case",
                str(synthetic.case),
                "--status",
                "INTERNALLY_AUDITED_CANDIDATE",
                "--final-claim",
                final_claim,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("candidate generation 2", result.stdout)

    def test_modified_audit_report_blocks_release(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            synthetic = SyntheticCase(Path(temporary))
            final_claim = synthetic.complete()
            report = synthetic.case / "audit" / "clean_room-report.md"
            report.write_text("mutated after audit\n", encoding="utf-8")
            result = run_script(
                "release_gate.py",
                "--case",
                str(synthetic.case),
                "--status",
                "INTERNALLY_AUDITED_CANDIDATE",
                "--final-claim",
                final_claim,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("report changed after completion", result.stdout)

    def test_modified_supporting_proof_blocks_release(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            synthetic = SyntheticCase(Path(temporary))
            final_claim = synthetic.complete()
            support = synthetic.case / "claims" / "lemma-proof.md"
            support.write_text("mutated after candidate freeze\n", encoding="utf-8")
            result = run_script(
                "release_gate.py",
                "--case",
                str(synthetic.case),
                "--status",
                "INTERNALLY_AUDITED_CANDIDATE",
                "--final-claim",
                final_claim,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Frozen artifact changed after audit", result.stdout)

    def test_omitted_frozen_artifact_blocks_release(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            synthetic = SyntheticCase(Path(temporary))
            final_claim = synthetic.complete()
            freeze_path = synthetic.case / "audit" / "candidate_freeze.json"
            freeze = json.loads(freeze_path.read_text(encoding="utf-8"))
            freeze["artifacts"].pop("claims_ledger")
            write_json(freeze_path, freeze)
            result = run_script(
                "release_gate.py",
                "--case",
                str(synthetic.case),
                "--status",
                "INTERNALLY_AUDITED_CANDIDATE",
                "--final-claim",
                final_claim,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(
                "Required frozen artifact omitted: state/claims.jsonl",
                result.stdout,
            )

    def test_open_major_finding_blocks_release(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            synthetic = SyntheticCase(Path(temporary))
            final_claim = synthetic.complete()
            run_script(
                "add_audit_finding.py",
                "--case",
                str(synthetic.case),
                "--lane",
                "dependency",
                "--severity",
                "major",
                "--status",
                "open",
                "--claim-id",
                final_claim,
                "--issue",
                "A synthetic major dependency gap.",
            )
            result = run_script(
                "release_gate.py",
                "--case",
                str(synthetic.case),
                "--status",
                "INTERNALLY_AUDITED_CANDIDATE",
                "--final-claim",
                final_claim,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("fatal/major audit finding", result.stdout)

    def test_complete_candidate_gates_and_packages(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            synthetic = SyntheticCase(Path(temporary))
            final_claim = synthetic.complete()
            gate = run_script(
                "release_gate.py",
                "--case",
                str(synthetic.case),
                "--status",
                "INTERNALLY_AUDITED_CANDIDATE",
                "--final-claim",
                final_claim,
            )
            self.assertIn("PASS", gate.stdout)

            package_result = run_script(
                "package_release.py",
                "--case",
                str(synthetic.case),
            )
            archive = Path(package_result.stdout.strip())
            manifest_path = archive.with_suffix(archive.suffix + ".manifest.json")
            self.assertTrue(archive.is_file())
            self.assertTrue(manifest_path.is_file())
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            self.assertEqual(
                hashlib.sha256(archive.read_bytes()).hexdigest(),
                manifest["archive_sha256"],
            )
            with zipfile.ZipFile(archive) as package:
                self.assertIsNone(package.testzip())
                names = package.namelist()
                self.assertFalse(any(name.endswith(".zip") for name in names))
                self.assertIn(
                    f"{synthetic.case_id}/claims/lemma-proof.md",
                    names,
                )
                for name, expected_hash in manifest["files"].items():
                    self.assertEqual(
                        hashlib.sha256(package.read(name)).hexdigest(),
                        expected_hash,
                    )

    def test_packager_revalidates_after_post_gate_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            synthetic = SyntheticCase(Path(temporary))
            final_claim = synthetic.complete()
            run_script(
                "release_gate.py",
                "--case",
                str(synthetic.case),
                "--status",
                "INTERNALLY_AUDITED_CANDIDATE",
                "--final-claim",
                final_claim,
            )
            candidate = synthetic.case / "proof" / "candidate_proof.tex"
            candidate.write_text("mutated after gate\n", encoding="utf-8")
            result = run_script(
                "package_release.py",
                "--case",
                str(synthetic.case),
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("revalidation failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
