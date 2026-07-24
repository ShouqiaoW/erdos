# Literature and information firewall

## Modes

### benchmark_blind

Use only ordinary background sources and standard named theorems. Do not search
for the exact problem, its ID, exact distinctive formula, or proof claims.

### background_only

Search nearby areas, standard machinery, and cited foundational papers.
Do not retrieve exact-problem proof claims until the candidate proof is frozen.

### full_research

Search exact prior art from the beginning. Record which ideas came from which
sources. Do not claim independent discovery.

## Librarian separation

The prior-art librarian should operate in a separate context.

Before candidate freeze in blind/background modes, it may report:

- whether the problem appears already resolved;
- whether it is equivalent to a major conjecture;
- whether a known counterexample exists;
- which background theorem families are likely relevant;
- which sources must be checked after freeze.

It should withhold exact solution mechanisms from the root unless required to
prevent wasted work or a false public claim.

## Citation ledger

Each external theorem or idea records:

- stable identifier;
- title/authors;
- publication date;
- source URL or bibliographic key;
- exact proposition used;
- where it enters the claim graph;
- whether it was seen before or after candidate freeze.

## Novelty language

Allowed:

- “rediscovery of a known argument”;
- “appears equivalent to known proof X”;
- “contains a potentially new lemma, prior-art search incomplete”;
- “no matching result found in the searched sources.”

Forbidden without strong evidence:

- “first proof”;
- “novel solution”;
- “unprecedented”;
- “independently solved” when exact prior art was visible.
