# JSP-000812 literal framing proof

This repository formalizes a counterexample to the **published JSP-000812 wording**:

> Are representation counts as sums of prime powers unbounded when the number of summands equals the exponent?

The maintained historical source is Erdős problem #979. Its statement explicitly assumes `k ≥ 2` before asking whether the representation counts for

`n = p₁^k + ··· + p_k^k`

are unbounded. The JSP wording omits that lower bound.

Under the literal JSP wording, positive exponent `k = 1` is allowed. Then a representation is just

`n = p`,

with one prime summand. For a fixed `n`, there is therefore at most one such representation. In particular, two distinct representations can never occur, so the representation counts are not unbounded.

The Lean development models representations as multisets of exactly `k` prime bases. The endpoint theorem proves the negation of the literal positive-exponent statement by using `k = 1` and requested multiplicity `2`.

This repository does **not** claim to solve historical Erdős #979 for `k ≥ 2`.

## Lean evidence

- Lean: `leanprover/lean4:v4.33.0`
- mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`
- Proof source: `JSP000812/Solution.lean`
- Theorem: `JSP000812.jsp_000812_literal`
- Axiom audit: `Audit.lean`

Reproduce with:

```bash
lake exe cache get
lake build
lake env lean JSP000812.lean
lake env lean Audit.lean
```

Historical source: https://www.erdosproblems.com/979
