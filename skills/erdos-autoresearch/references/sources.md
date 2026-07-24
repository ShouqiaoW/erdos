# Sources and provenance

## Primary workflow source

Shouqiao Wang, `ShouqiaoW/erdos`:

- https://github.com/ShouqiaoW/erdos
- https://github.com/ShouqiaoW/erdos/tree/main/390
- https://github.com/ShouqiaoW/erdos/tree/main/486
- https://github.com/ShouqiaoW/erdos/tree/main/536
- https://github.com/ShouqiaoW/erdos/tree/main/788
- https://github.com/ShouqiaoW/erdos/tree/main/1002
- https://github.com/ShouqiaoW/erdos/tree/main/1038

Observed recurring design patterns:

- exact restatement of definitions and quantifiers;
- explicit affirmative and negative completion conditions;
- long lists of insufficient partial results;
- domain-specific failure modes and edge cases;
- independent, diverse approach families;
- dynamic route allocation rather than a fixed agent split;
- aggressive counterexample search;
- computation treated as evidence unless converted into a certificate;
- adversarial audits before a proof is returned;
- LaTeX, Python, and Lean artifacts.

This package paraphrases and generalizes those patterns. It does not reproduce
the repository prompts wholesale.

## Worked prompt exemplar

OpenAI, “Prompt Used for ‘A Proof of the Cycle Double Cover Conjecture’”:

- https://cdn.openai.com/pdf/04d1d1e4-bc75-476a-97cf-49055cd98d31/cdc_prompt.pdf
- preserved verbatim in `openai-cdc-example-prompt.txt`;
- interpreted for this Skill in `openai-cdc-example-notes.md`.

The exemplar supplies the affirmative-proof premise, dynamic multi-agent search
loop, adversarial audit pattern, and minimum eight-hour return floor.

## Portable Agent Skills format

Agent Skills, “Specification”:

- https://agentskills.io/specification

Relevant format points:

- a skill is a directory with a required `SKILL.md`;
- optional `scripts/`, `references/`, and `assets/`;
- `SKILL.md` requires `name` and `description`;
- relative file references resolve from the skill root;
- the main instructions should remain below 500 lines.

## Cross-agent installation model

Vercel Labs, `skills`:

- https://github.com/vercel-labs/skills

The repository installation instructions follow its target-selection model:

- one canonical skill source;
- explicit project or user scope;
- explicit agent targets;
- symlink installation by default and copy fallback;
- support for Claude Code, Codex, Cursor, Gemini CLI, and GitHub Copilot.

Primary client documentation:

- https://learn.chatgpt.com/docs/build-skills
- https://code.claude.com/docs/en/skills
- https://cursor.com/docs/skills
- https://geminicli.com/docs/cli/using-agent-skills/
- https://docs.github.com/en/copilot/how-tos/copilot-on-github/customize-copilot/customize-cloud-agent/add-skills
