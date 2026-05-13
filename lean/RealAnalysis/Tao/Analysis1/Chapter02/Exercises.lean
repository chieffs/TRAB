import RealAnalysis.Tao.Analysis1.Chapter02.Lemmas
import Mathlib.Tactic

/-!
### Chapter 2 — exercises (Tao 4th ed.)

Statements from `Tao-Chapter-2-Note.md`. Replace each `sorry` with a proof
using only definitions / axioms / lemmas from `Axioms.lean` and `Lemmas.lean`
(and Mathlib **tactics** — no `Mathlib.Data` lemmas).
-/

namespace RealAnalysis.Tao.Analysis1.Ch02

open TaoNat (zero succ)

/-! ### Exercise 2.2.1 — Tao Proposition 2.2.5 (associativity of addition) -/

/-- Tao Proposition 2.2.5 / Exercise 2.2.1: `(a + b) + c = a + (b + c)`. -/
theorem exercise_2_2_1 (a b c : TaoNat) : (a + b) + c = a + (b + c) := by
  sorry

/-! ### Exercise 2.2.2 — Tao Lemma 2.2.10 (predecessor) -/

/-- Tao Lemma 2.2.10 / Exercise 2.2.2: every positive `a` has a unique predecessor. -/
theorem exercise_2_2_2 (a : TaoNat) (ha : TaoPositive a) : ∃! b : TaoNat, succ b = a := by
  sorry

/-! ### Exercise 2.2.3 — Tao Proposition 2.2.12 (properties of order) -/

/-- (1) Order is reflexive. -/
theorem exercise_2_2_3_reflexive (a : TaoNat) : TaoGe a a := by
  sorry

/-- (2) Order is transitive. -/
theorem exercise_2_2_3_transitive {a b c : TaoNat} (hab : TaoGe a b) (hbc : TaoGe b c) :
    TaoGe a c := by
  sorry

/-- (3) Order is antisymmetric. -/
theorem exercise_2_2_3_antisymmetric {a b : TaoNat} (hab : TaoGe a b) (hba : TaoGe b a) :
    a = b := by
  sorry

/-- (4) Addition preserves (Tao) order on both sides. -/
theorem exercise_2_2_3_add_preserves {a b c : TaoNat} : TaoGe a b ↔ TaoGe (a + c) (b + c) := by
  sorry

/-- (5) `a < b` iff `a++ ≤ b` in Tao’s sense (`TaoGe (succ a) b`). -/
theorem exercise_2_2_3_succ_iff {a b : TaoNat} : TaoGt a b ↔ TaoGe (succ a) b := by
  sorry

/-- (6) `a < b` iff `b = a + d` for some positive `d`. -/
theorem exercise_2_2_3_lt_iff_add_positive {a b : TaoNat} :
    TaoGt a b ↔ ∃ d, TaoPositive d ∧ b = a + d := by
  sorry

/-! ### Exercise 2.2.4 — Tao Proposition 2.2.13 (trichotomy) -/

/--
Tao Proposition 2.2.13 (trichotomy) / Exercise 2.2.4:
exactly one of `a < b`, `a = b`, `a > b` holds (Tao’s strict order).
-/
theorem exercise_2_2_4_trichotomy (a b : TaoNat) :
    (TaoGt a b ∨ a = b ∨ TaoGt b a) ∧
      (¬(TaoGt a b ∧ a = b)) ∧
      (¬(TaoGt a b ∧ TaoGt b a)) ∧
      (¬(a = b ∧ TaoGt b a)) := by
  sorry

/-! ### Exercise 2.2.5 — strong induction -/

/--
Tao strong principle of induction / Exercise 2.2.5:
from a base `m0`, if `P(m)` follows from `P` on all `m'` with `m0 ≤ m' < m`
(`TaoGe m' m0` and `TaoLt m' m`), then `P(m)` holds for all `m ≥ m0`.
-/
theorem exercise_2_2_5_strong_induction
    (m0 : TaoNat) (P : TaoNat → Prop)
    (h : ∀ m, TaoGe m m0 → (∀ m', TaoGe m' m0 → TaoLt m' m → P m') → P m) :
    ∀ m, TaoGe m m0 → P m := by
  sorry

end RealAnalysis.Tao.Analysis1.Ch02
