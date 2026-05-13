import RealAnalysis.Tao.Analysis1.Chapter02.Axioms
import Mathlib.Tactic

/-!
### Lemmas / propositions / corollaries from Chapter 2 (non-exercise items)

From `vault/book/Tao-Chapter-2-Note.md`, everything whose proof you **did not**
reserve for a numbered exercise is proved here. Items tagged as exercises
2.2.1–2.2.5 are stated with `sorry` in `Exercises.lean`.
-/

namespace RealAnalysis.Tao.Analysis1.Ch02

/-- Tao Lemma 2.2.2: `n + 0 = n`. -/
lemma lemma_2_2_2 (n : ℕ) : n + 0 = n :=
  Nat.add_zero n

/-- Tao Lemma 2.2.3: `n + (m++) = (n + m)++` (here `m++` is `Nat.succ m`). -/
lemma lemma_2_2_3 (n m : ℕ) : n + m.succ = (n + m).succ :=
  (Nat.add_succ n m).symm

/-- Tao Proposition 2.2.4: addition is commutative. -/
theorem prop_2_2_4 (n m : ℕ) : n + m = m + n :=
  Nat.add_comm n m

/-! ### Tao Proposition 2.2.6 (cancellation) -/

/-- Tao Proposition 2.2.6: if `a + b = a + c` then `b = c`. -/
theorem prop_2_2_6 {a b c : ℕ} (h : a + b = a + c) : b = c :=
  Nat.add_left_cancel h

/-! ### Tao Proposition 2.2.8 and Corollary 2.2.9 -/

/-- Tao Proposition 2.2.8: if `a` is positive and `b` is any natural, then `a + b` is positive. -/
theorem prop_2_2_8 {a b : ℕ} (ha : TaoPositive a) : TaoPositive (a + b) := by
  rw [TaoPositive] at ha ⊢
  intro hab
  rcases Nat.add_eq_zero.mp hab with ⟨ha0, _⟩
  exact ha ha0

/-- Tao Corollary 2.2.9: if `a + b = 0` then `a = 0` and `b = 0`. -/
theorem corollary_2_2_9 {a b : ℕ} (h : a + b = 0) : a = 0 ∧ b = 0 :=
  Nat.add_eq_zero.mp h

end RealAnalysis.Tao.Analysis1.Ch02
