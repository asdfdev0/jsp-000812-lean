import Mathlib

namespace JSP000812

/-- A representation of `n` at exponent `k` is a multiset of exactly `k`
prime bases whose `k`-th powers sum to `n`. Using multisets makes the
representation convention unordered, but the `k = 1` counterexample below
is independent of ordered-vs-unordered conventions. -/
def ValidRepresentation (n k : ℕ) (P : Multiset ℕ) : Prop :=
  P.card = k ∧
    (∀ p ∈ P, Nat.Prime p) ∧
    n = (P.map (fun p => p ^ k)).sum

/-- `n` has at least `r` distinct representations at exponent `k`. -/
def HasAtLeastRepresentations (n k r : ℕ) : Prop :=
  ∃ reps : Fin r → Multiset ℕ,
    Function.Injective reps ∧
    ∀ i, ValidRepresentation n k (reps i)

/-- Representation counts are unbounded at exponent `k`. -/
def UnboundedAtExponent (k : ℕ) : Prop :=
  ∀ r : ℕ, ∃ n : ℕ, HasAtLeastRepresentations n k r

/-- Literal reading of the JSP wording: every positive exponent is allowed.
The historical source instead restricts to `k ≥ 2`. -/
def LiteralStatement : Prop :=
  ∀ k : ℕ, 0 < k → UnboundedAtExponent k

lemma one_summand_unique {n : ℕ} {P : Multiset ℕ}
    (hP : ValidRepresentation n 1 P) : P = {n} := by
  rcases Multiset.card_eq_one.mp hP.1 with ⟨p, rfl⟩
  have hnp : n = p := by
    simpa [ValidRepresentation] using hP.2.2
  subst p
  rfl

/-- The published JSP wording omits the historical lower bound `k ≥ 2`.
At `k = 1`, every valid representation of a fixed `n` is the same singleton
multiset `{n}`, so there cannot be two distinct representations. -/
theorem jsp_000812_literal : ¬ LiteralStatement := by
  intro h
  have h1 : UnboundedAtExponent 1 := h 1 (by omega)
  obtain ⟨n, reps, hinj, hvalid⟩ := h1 2
  have h0 : reps 0 = ({n} : Multiset ℕ) := one_summand_unique (hvalid 0)
  have h1' : reps 1 = ({n} : Multiset ℕ) := one_summand_unique (hvalid 1)
  have hEq : reps 0 = reps 1 := h0.trans h1'.symm
  have : (0 : Fin 2) = 1 := hinj hEq
  norm_num at this

end JSP000812
