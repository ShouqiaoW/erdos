# Formalization strategy

## Start early

Formalize early enough to influence theorem decomposition. Do not wait until a
long prose proof has accumulated hidden coercions, undefined edge cases, or
unstated finiteness assumptions.

## Priority order

1. theorem statement;
2. definitions and domains;
3. degenerate cases;
4. highest-risk lemmas;
5. finite certificate checker;
6. remaining dependency cone;
7. final theorem.

## Scope manifest

Record for every item:

- file;
- declaration name;
- status;
- axioms or classical principles used;
- imported libraries;
- toolchain version;
- whether the declaration is final or only analogous.

Example statuses:

```text
not_started
statement_encoded
checked
checked_with_axioms
prose_only
blocked
```

## No scope inflation

The phrases below are materially different:

- “The definitions compile in Lean.”
- “Three supporting lemmas are machine-checked.”
- “The finite certificate checker is machine-checked.”
- “The final theorem is machine-checked.”

Use only the exact applicable statement.

## Trust base

Document:

- proof assistant version;
- kernel;
- external tactics;
- native-decide or code generation;
- oracle use;
- admitted statements;
- unsafe axioms.

Any `sorry`, admitted theorem, or unverified generated code prevents a
`machine_checked` final claim.
