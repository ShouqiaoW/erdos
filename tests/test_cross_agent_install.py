from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


REPOSITORY = Path(__file__).resolve().parents[1]
SKILL_NAME = "erdos-autoresearch"
SKILLS_CLI_VERSION = "1.5.20"
TARGETS = [
    "claude-code",
    "codex",
    "cursor",
    "gemini-cli",
    "github-copilot",
]
TARGET_LABELS = [
    "Claude Code",
    "Codex",
    "Cursor",
    "Gemini CLI",
    "GitHub Copilot",
]
BUN = shutil.which("bun")


def tree_hashes(root: Path) -> dict[str, str]:
    return {
        str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(root.rglob("*"))
        if path.is_file()
    }


@unittest.skipUnless(BUN, "bun is required for cross-agent installer tests")
class CrossAgentInstallTests(unittest.TestCase):
    def install(
        self,
        root: Path,
        *,
        global_scope: bool = False,
        copy: bool = False,
    ) -> tuple[Path, Path, subprocess.CompletedProcess[str]]:
        project = root / "project"
        home = root / "home"
        project.mkdir()
        home.mkdir()
        command = [
            str(BUN),
            "x",
            f"skills@{SKILLS_CLI_VERSION}",
            "add",
            str(REPOSITORY),
            "--skill",
            SKILL_NAME,
            "--agent",
            *TARGETS,
            "--yes",
        ]
        if global_scope:
            command.append("--global")
        if copy:
            command.append("--copy")
        environment = {
            **os.environ,
            "HOME": str(home),
            "BUN_INSTALL_CACHE_DIR": os.environ.get(
                "BUN_INSTALL_CACHE_DIR",
                str(Path.home() / ".bun" / "install" / "cache"),
            ),
        }
        result = subprocess.run(
            command,
            cwd=project,
            env=environment,
            text=True,
            capture_output=True,
            check=False,
            timeout=120,
        )
        return project, home, result

    def test_project_install_uses_shared_canonical_skill(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            project, _, result = self.install(Path(temporary))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            canonical = (
                project / ".agents" / "skills" / "erdos-autoresearch"
            )
            claude = (
                project / ".claude" / "skills" / "erdos-autoresearch"
            )
            self.assertTrue((canonical / "SKILL.md").is_file())
            self.assertTrue(
                os.access(canonical / "scripts" / "release_gate.py", os.X_OK)
            )
            self.assertTrue(claude.is_symlink())
            self.assertEqual(claude.resolve(), canonical.resolve())
            self.assertTrue((project / "skills-lock.json").is_file())
            for label in TARGET_LABELS:
                self.assertIn(label, result.stdout)

    def test_project_copy_mode_avoids_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            project, _, result = self.install(Path(temporary), copy=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            canonical = (
                project / ".agents" / "skills" / "erdos-autoresearch"
            )
            claude = (
                project / ".claude" / "skills" / "erdos-autoresearch"
            )
            self.assertTrue(canonical.is_dir())
            self.assertTrue(claude.is_dir())
            self.assertFalse(canonical.is_symlink())
            self.assertFalse(claude.is_symlink())
            self.assertEqual(tree_hashes(canonical), tree_hashes(claude))

    def test_global_install_is_isolated_to_temporary_home(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            project, home, result = self.install(
                Path(temporary),
                global_scope=True,
            )
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            canonical = (
                home / ".agents" / "skills" / "erdos-autoresearch"
            )
            claude = (
                home / ".claude" / "skills" / "erdos-autoresearch"
            )
            self.assertTrue((canonical / "SKILL.md").is_file())
            self.assertTrue(claude.is_symlink())
            self.assertEqual(claude.resolve(), canonical.resolve())
            self.assertFalse((project / ".agents").exists())


if __name__ == "__main__":
    unittest.main()
