# Erdős proofs

Proofs of Erdős problems. Each proof has been carefully checked for correctness
with the help of AI. Some have also been formalized and machine-checked in Lean,
and formalization of the rest is in progress.

## Erdős Autoresearch skill

[`skills/erdos-autoresearch`](skills/erdos-autoresearch) packages the
repository's long-horizon proof-research method as a portable
[Agent Skill](https://agentskills.io/specification). It freezes the exact
problem, compiles an audited proof contract, manages independent research
routes and claim dependencies, attacks intermediate claims with
counterexamples, and refuses to package a result until an exact affirmative
candidate passes deterministic release checks.

The skill deliberately:

- assumes a complete affirmative proof exists as a research premise;
- requires at least eight elapsed research hours before any terminal return;
- treats eight hours as a floor rather than a stopping time;
- refuses partial, plateau, no-go, and counterexample terminal results;
- uses `INTERNALLY_AUDITED_CANDIDATE` as its strongest automated status.

### Requirements

- a client that supports the Agent Skills standard;
- [`uv`](https://docs.astral.sh/uv/) to run the bundled Python 3.11+ utilities;
- the host client's normal tools for browsing, computation, subagents, LaTeX,
  or Lean when those lanes are enabled.

The deterministic scripts use only the Python standard library.

### Install in Claude Code, Codex, Cursor, Gemini CLI, and Copilot

The recommended installer is Vercel's open-source
[`skills`](https://github.com/vercel-labs/skills) CLI. Project scope is the
default:

```bash
bunx skills add ShouqiaoW/erdos \
  --skill erdos-autoresearch \
  --agent claude-code codex cursor gemini-cli github-copilot \
  --yes
```

Install for the current user instead:

```bash
bunx skills add ShouqiaoW/erdos \
  --skill erdos-autoresearch \
  --agent claude-code codex cursor gemini-cli github-copilot \
  --global \
  --yes
```

The installer keeps one canonical copy and symlinks agent-specific discovery
paths. Add `--copy` when symlinks are unavailable or undesirable.

To test a checkout before this branch is merged, replace `ShouqiaoW/erdos` with
the checkout's absolute path.

### Manual installation

Copy or symlink the complete `skills/erdos-autoresearch` directory, not only
`SKILL.md`.

| Client | Project scope | User scope |
|---|---|---|
| Claude Code | `.claude/skills/erdos-autoresearch` | `~/.claude/skills/erdos-autoresearch` |
| Codex | `.agents/skills/erdos-autoresearch` | `~/.agents/skills/erdos-autoresearch` |
| Cursor | `.agents/skills/erdos-autoresearch` | `~/.agents/skills/erdos-autoresearch` |
| Gemini CLI | `.agents/skills/erdos-autoresearch` | `~/.agents/skills/erdos-autoresearch` |
| GitHub Copilot | `.agents/skills/erdos-autoresearch` | `~/.agents/skills/erdos-autoresearch` |

Agent-specific aliases such as `.cursor/skills`, `.gemini/skills`, and
`~/.copilot/skills` also work in their respective clients. The shared
`.agents/skills` location avoids duplicate project copies where the client
supports it.

### Invoke

Use the client's skill picker or mention the skill explicitly. For example:

```text
Use $erdos-autoresearch on the exact problem in problem.md. Keep the default
affirmative-proof premise and eight-hour minimum.
```

Do not invoke the skill merely to test installation: a real run is designed to
continue for hours. Use the validation commands below instead.

### Validate without starting a research run

```bash
uv run --no-project \
  skills/erdos-autoresearch/scripts/skill_doctor.py \
  --skill-dir skills/erdos-autoresearch

PYTHONDONTWRITEBYTECODE=1 \
  uv run --no-project -m unittest discover -s tests -v
```

The test suite exercises every CLI entry point, a complete synthetic case,
release rejection paths, audit-generation invalidation, package integrity, and
cross-agent installation in isolated temporary directories. It never launches
the long-running research workflow.
