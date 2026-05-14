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
  induction a with
  | zero =>
    rw [zero_add,zero_add]
  | succ a ih =>
    rw [succ_add,succ_add,succ_add,ih]



/-! ### Exercise 2.2.2 — Tao Lemma 2.2.10 (predecessor) -/

/-- Tao Lemma 2.2.10 / Exercise 2.2.2: every positive `a` has a unique predecessor. -/
theorem exercise_2_2_2 (a : TaoNat) (ha : TaoPositive a) :  ∃! b : TaoNat, succ b = a := by
  have h_exists : ∃ b : TaoNat, succ b = a := by
    induction a with
      |zero =>
        unfold TaoPositive at ha
        contradiction
      | succ ih => use ih
  rcases h_exists with ⟨b, hb⟩
  use b
  constructor
  exact hb
  intro c hc
  rw [<- hb] at hc
  apply axiom_2_4 at hc
  exact hc





/-! ### Exercise 2.2.3 — Tao Proposition 2.2.12 (properties of order) -/

/-- (1) Order is reflexive. -/
theorem exercise_2_2_3_reflexive (a : TaoNat) : TaoGe a a := by
  unfold TaoGe
  use zero
  rw [prop_2_2_4,zero_add]


/-- (2) Order is transitive. -/
theorem exercise_2_2_3_transitive {a b c : TaoNat} (hab : TaoGe a b) (hbc : TaoGe b c) :
    TaoGe a c := by
    unfold TaoGe at hab
    unfold TaoGe at hbc
    rcases hab with ⟨k,hk⟩
    rcases hbc with ⟨m, hm⟩
    rw [hm,exercise_2_2_1] at hk
    unfold TaoGe
    use (m+k)





/-- (3) Order is antisymmetric. -/
theorem exercise_2_2_3_antisymmetric {a b : TaoNat} (hab : TaoGe a b) (hba : TaoGe b a) :
    a = b := by
    unfold TaoGe at hab
    unfold TaoGe at hba
    rcases hab with ⟨k,hk⟩
    rcases hba with ⟨m, hm⟩
    rw [hm,exercise_2_2_1] at hk
    have h_cancel : a + zero = a + (m + k) := by
      rw [lemma_2_2_2]
      exact hk
    have h_zero_sum := prop_2_2_6 h_cancel
    have h_zeros := corollary_2_2_9 h_zero_sum.symm
    rcases h_zeros with ⟨hm_zero, hk_zero⟩
    rw [hm_zero] at hm
    change b = a + zero at hm
    rw [lemma_2_2_2] at hm
    rw [hm]


/-- (4) Addition preserves (Tao) order on both sides. -/
theorem exercise_2_2_3_add_preserves {a b c : TaoNat} : TaoGe a b ↔ TaoGe (a + c) (b + c) := by
  constructor
  ·-- Forward direction: (a ≥ b) → (a + c ≥ b + c)
    intro h
    unfold TaoGe at h
    rcases h with ⟨ k,h_k ⟩
    use k
    rw [h_k,exercise_2_2_1,prop_2_2_4 k c,exercise_2_2_1]
  · -- Backward direction: (a + c ≥ b + c) → (a ≥ b)
    intro h_ac_bc
    unfold TaoGe at h_ac_bc ⊢
    rcases h_ac_bc with ⟨ k,h_k ⟩
    use k
    conv at h_k=>
      rhs
      rw[exercise_2_2_1, prop_2_2_4 c k , <- exercise_2_2_1, prop_2_2_4]
    rw [prop_2_2_4] at h_k
    apply prop_2_2_6 at h_k
    use h_k


/-- (5) `a < b` iff `a++ ≤ b` in Tao’s sense (`TaoGe (succ a) b`). -/
theorem exercise_2_2_3_succ_iff {a b : TaoNat} : TaoGt b a ↔ TaoGe b (succ a):= by
  constructor
  · -- Forward direction
    intro h
    rcases h with ⟨h,h_ineq⟩
    unfold TaoGe at h ⊢
    rcases h with ⟨k,h_k⟩
    have h_k_pos : TaoPositive k := by
      intro h_zero
      rw [h_zero] at h_k
      change b = a+zero at h_k
      rw [lemma_2_2_2] at h_k
      contradiction
    have h_k_exists := exercise_2_2_2 k h_k_pos
    rcases h_k_exists with ⟨m, h_m⟩
    use m
    rw [h_k,prop_2_2_4,succ_add,prop_2_2_4]
    conv =>
      rhs
      rw[prop_2_2_4,<- succ_add,prop_2_2_4]
    rw [h_m.left]

  · -- Backward direction
    intro h_b
    unfold TaoGe at h_b
    rcases h_b with ⟨ k,h_k ⟩
    unfold TaoGt
    constructor
    ·
      unfold TaoGe
      use k.succ
      conv =>
        rhs
        rw[prop_2_2_4,succ_add,prop_2_2_4,<-succ_add]
      rw [h_k]
    · -- Second goal: Prove a ≠ b
      intro h_eq
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
