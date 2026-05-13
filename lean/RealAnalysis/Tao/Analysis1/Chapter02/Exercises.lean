import RealAnalysis.Tao.Analysis1.Chapter02.Lemmas
import Mathlib.Tactic

/-!
### Chapter 2 — exercises (Tao 4th ed.)

Statements you marked in `Tao-Chapter-2-Note.md` as exercise proofs. Replace
each `sorry` with your own proof (you may use earlier `Axioms` / `Lemmas`).
-/

namespace RealAnalysis.Tao.Analysis1.Ch02

/-! ### Exercise 2.2.1 — Tao Proposition 2.2.5 (associativity of addition) -/

/-- Tao Proposition 2.2.5 / Exercise 2.2.1: `(a + b) + c = a + (b + c)`. -/
theorem exercise_2_2_1 (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  sorry

/-! ### Exercise 2.2.2 — Tao Lemma 2.2.10 (predecessor) -/

/-- Tao Lemma 2.2.10 / Exercise 2.2.2: every positive `a` has a unique predecessor. -/
theorem exercise_2_2_2 (a : ℕ) (ha : TaoPositive a) : ∃! b : ℕ, b.succ = a := by
  sorry

/-! ### Exercise 2.2.3 — Tao Proposition 2.2.12 (properties of order) -/

/-- (1) Order is reflexive. -/
theorem exercise_2_2_3_reflexive (a : ℕ) : TaoGe a a := by
  sorry

/-- (2) Order is transitive. -/
theorem exercise_2_2_3_transitive {a b c : ℕ} (hab : TaoGe a b) (hbc : TaoGe b c) :
    TaoGe a c := by
  sorry

/-- (3) Order is antisymmetric. -/
theorem exercise_2_2_3_antisymmetric {a b : ℕ} (hab : TaoGe a b) (hba : TaoGe b a) :
    a = b := by
  sorry

/-- (4) Addition preserves (Tao) order on both sides. -/
theorem exercise_2_2_3_add_preserves {a b c : ℕ} : TaoGe a b ↔ TaoGe (a + c) (b + c) := by
  sorry

/-- (5) `a < b` iff `a++ ≤ b` (Tao’s `++` is `Nat.succ`). -/
theorem exercise_2_2_3_succ_iff {a b : ℕ} : TaoGt a b ↔ TaoGe a.succ b := by
  sorry

/-- (6) `a < b` iff `b = a + d` for some positive `d`. -/
theorem exercise_2_2_3_lt_iff_add_positive {a b : ℕ} :
    TaoGt a b ↔ ∃ d, TaoPositive d ∧ b = a + d := by
  sorry

/-! ### Exercise 2.2.4 — Tao Proposition 2.2.13 (trichotomy) -/

/--
Tao Proposition 2.2.13 (trichotomy) / Exercise 2.2.4:
exactly one of `a < b`, `a = b`, `a > b` holds.

We package “exactly one” as: pairwise incompatible disjuncts whose disjunction
still holds (refine as you prefer).
-/
theorem exercise_2_2_4_trichotomy (a b : ℕ) :
    (TaoGt a b ∨ a = b ∨ TaoGt b a) ∧
      (¬(TaoGt a b ∧ a = b)) ∧
      (¬(TaoGt a b ∧ TaoGt b a)) ∧
      (¬(a = b ∧ TaoGt b a)) := by
  sorry

/-! ### Exercise 2.2.5 — strong induction (second “2.2.13” in your note) -/

/--
Tao strong principle of induction / Exercise 2.2.5:
from a base `m0`, if `P(m)` follows from `P` on all `m'` with `m0 ≤ m' < m`,
then `P(m)` holds for all `m ≥ m0`.
-/
theorem exercise_2_2_5_strong_induction
    (m0 : ℕ) (P : ℕ → Prop)
    (h : ∀ m, m0 ≤ m → (∀ m', m0 ≤ m' → m' < m → P m') → P m) :
    ∀ m, m0 ≤ m → P m := by
  sorry

end RealAnalysis.Tao.Analysis1.Ch02
