import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
### Axiomatic layer (Tao *Analysis I*, 4th ed. — Chapter 2: natural numbers)

This file matches `vault/book/Tao-Chapter-2-Note.md`: **definitions** and the
book’s **Peano axioms** as facts about Mathlib’s `ℕ` (which is built from the
same rules). Exercise proofs live in `Exercises.lean`.
-/

namespace RealAnalysis.Tao.Analysis1.Ch02

/-! ## Key definitions (Obsidian: Key definitions) -/

/-- Tao 2.2.11: `n ≥ m` iff `n = m + a` for some natural `a`. Same as `m ≤ n`. -/
def TaoGe (n m : ℕ) : Prop :=
  ∃ a : ℕ, n = m + a

/-- Tao 2.2.11: strict order — `n > m` means `n ≥ m` and `n ≠ m`. -/
def TaoGt (n m : ℕ) : Prop :=
  TaoGe n m ∧ n ≠ m

/-- Tao 2.2.7: a natural number is **positive** iff it is not `0`. -/
def TaoPositive (n : ℕ) : Prop :=
  n ≠ 0

/-- Tao 2.1.3: `1 := 0++`. -/
abbrev tao_one : ℕ :=
  Nat.succ 0

/-- Tao 2.1.3: `2 := (0++)++`. -/
abbrev tao_two : ℕ :=
  Nat.succ tao_one

/-- Tao 2.1.3: `3 := ((0++)++)++`. -/
abbrev tao_three : ℕ :=
  Nat.succ tao_two

/-! ## Axioms 2.1–2.5 as theorems for `ℕ` -/

/-- Tao 2.1: `0` is a natural number. -/
theorem axiom_2_1 : (0 : ℕ) = 0 :=
  rfl

/-- Tao 2.2: successors of natural numbers are natural numbers (closure of `succ`). -/
theorem axiom_2_2 (n : ℕ) : ∃ m : ℕ, m = n.succ :=
  ⟨n.succ, rfl⟩

/-- Tao 2.3: `0` is not a successor. -/
theorem axiom_2_3 (n : ℕ) : n.succ ≠ 0 :=
  Nat.succ_ne_zero n

/-- Tao 2.4: successor is injective / “different numbers have different successors”. -/
theorem axiom_2_4 {n m : ℕ} (h : n.succ = m.succ) : n = m :=
  Nat.succ.inj h

/-- Tao 2.5: ordinary induction on `ℕ` (principle of mathematical induction). -/
theorem axiom_2_5 (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P n.succ) : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hs n ih

/-! ## Bridge lemmas (order) -/

lemma tao_ge_iff_le (n m : ℕ) : TaoGe n m ↔ m ≤ n := by
  rw [TaoGe]
  exact Iff.symm Nat.le_iff_exists_add

lemma tao_gt_iff_lt (n m : ℕ) : TaoGt n m ↔ m < n := by
  rw [TaoGt, tao_ge_iff_le, Nat.lt_iff_le_and_ne]
  exact Iff.and_congr Iff.rfl ne_comm

lemma tao_positive_iff (n : ℕ) : TaoPositive n ↔ 0 < n := by
  rw [TaoPositive]
  exact Iff.symm Nat.pos_iff_ne_zero

lemma tao_one_eq_one : tao_one = (1 : ℕ) :=
  rfl

lemma tao_two_eq_two : tao_two = (2 : ℕ) :=
  rfl

lemma tao_three_eq_three : tao_three = (3 : ℕ) :=
  rfl

end RealAnalysis.Tao.Analysis1.Ch02
