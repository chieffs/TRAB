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
      rw [h_eq] at h_k
      conv at h_k=>
        rhs
        rw [succ_add,prop_2_2_4,<- succ_add,prop_2_2_4]
      conv at h_k =>
        lhs
        rw [<- lemma_2_2_2 a]
      apply prop_2_2_6 at h_k
      contradiction



/-- (6) `a < b` iff `b = a + d` for some positive `d`. -/
theorem exercise_2_2_3_lt_iff_add_positive {a b : TaoNat} :
    TaoGt b a ↔ ∃ d, TaoPositive d ∧ b = a + d := by
    constructor
    ·
      intro h_for
      rw [exercise_2_2_3_succ_iff] at h_for
      unfold TaoGe at h_for
      rcases h_for with ⟨k, h_k⟩
      use k.succ
      constructor
      ·
        unfold TaoPositive
        intro h_zero
        contradiction
      ·
        conv at h_k =>
          rhs
          rw [succ_add,prop_2_2_4,<- succ_add,prop_2_2_4]
        use h_k
    ·
      intro h_back
      unfold TaoGt
      constructor
      ·
        unfold TaoGe
        rcases h_back with ⟨d,h_d⟩
        use d
        apply h_d.right
      ·
        rcases h_back with ⟨ d,pos,eq⟩
        rw [eq]
        conv =>
          rhs
          rw [<- lemma_2_2_2 a]
        by_contra
        apply prop_2_2_6 at this
        contradiction




/-! ### Exercise 2.2.4 — Tao Proposition 2.2.13 (trichotomy) -/

/--
Tao Proposition 2.2.13 (trichotomy) / Exercise 2.2.4:
exactly one of `a < b`, `a = b`, `a > b` holds (Tao’s strict order).
-/
theorem exercise_2_2_4_trichotomy (a b : TaoNat) :
    (TaoGt b a ∨ a = b ∨ TaoGt a b) ∧
      (¬(TaoGt b a ∧ a = b)) ∧
      (¬(TaoGt b a ∧ TaoGt a b)) ∧
      (¬(a = b ∧ TaoGt a b)) := by
  constructor
  .
    induction a with
    | zero =>
      cases b with
      | zero =>
        right
        left
        rfl
      | succ d =>
        left
        unfold TaoGt
        constructor
        ·
          unfold TaoGe
          use d.succ
          rfl
        ·
          by_contra
          apply axiom_2_3 at this
          contradiction


    | succ a ih =>
      rcases ih with  h_gt | h_eq | h_lt
      ·
        rw [exercise_2_2_3_succ_iff] at h_gt
        unfold TaoGe at h_gt
        rcases h_gt with ⟨ k , h_ge ⟩
        cases k with
          | zero =>
            rw [lemma_2_2_2] at h_ge
            right
            left
            symm
            use h_ge
          | succ d =>
            left
            unfold TaoGt
            constructor
            .
              unfold TaoGe
              use d.succ
            .
              by_contra
              rw [h_ge] at this
              conv at this =>
                rhs
                rw [<- zero_add a.succ]
                apply prop_2_2_4
              apply prop_2_2_6 at this
              apply axiom_2_3 at this
              contradiction
      ·
        right
        right
        unfold TaoGt
        constructor
        .
          unfold TaoGe
          use zero.succ
          rw [h_eq]
          conv =>
            rhs
            rw [lemma_2_2_3, lemma_2_2_2]
        .
          rw [h_eq]
          by_contra
          rw [<- lemma_2_2_2 b,<- lemma_2_2_3] at this
          apply prop_2_2_6 at this
          apply axiom_2_3 at this
          contradiction
      .
        rw [exercise_2_2_3_succ_iff] at h_lt
        unfold TaoGe at h_lt
        rcases h_lt with ⟨ k , h_le ⟩
        cases k with
          | zero =>
            rw [lemma_2_2_2] at h_le
            right
            right
            unfold TaoGt
            constructor
            .
              unfold TaoGe
              use zero.succ.succ
              rw [h_le, lemma_2_2_3,lemma_2_2_3, lemma_2_2_2]
            .
              by_contra
              rw [h_le] at this
              rw [<- lemma_2_2_2 b,<- lemma_2_2_3,<- lemma_2_2_3] at this
              apply prop_2_2_6 at this
              apply axiom_2_3 at this
              contradiction
          | succ d =>
            right
            right
            unfold TaoGt
            constructor
            .
              unfold TaoGe
              use d.succ.succ.succ
              conv at h_le =>
                rhs
                rw [prop_2_2_4,lemma_2_2_3,prop_2_2_4,<-lemma_2_2_3]
              rw [h_le, <-lemma_2_2_3]
            .
              by_contra
              rw [h_le,prop_2_2_4,lemma_2_2_3,prop_2_2_4,<-lemma_2_2_3,<-lemma_2_2_3] at this
              conv at this =>
                rhs
                rw[<- lemma_2_2_2 b]
              apply prop_2_2_6 at this
              apply axiom_2_3 at this
              contradiction
  .
    constructor
    .
      by_contra
      rcases this with ⟨ hip_gt, hip_eq ⟩
      rw [hip_eq] at hip_gt
      unfold TaoGt at hip_gt
      rcases hip_gt with ⟨ hip_ge, hip_false ⟩
      contradiction
    .
      constructor
      .
        by_contra
        unfold TaoGt at this
        unfold TaoGe at this
        rcases this with ⟨h_left,h_right⟩
        rcases h_left with ⟨h_left,h_left_ineq⟩
        rcases h_right with ⟨h_right,h_right_ineq⟩
        rcases h_left with ⟨d,h_left⟩
        rcases h_right with ⟨k,h_right⟩
        rw [h_left] at h_right
        conv at h_right =>
          lhs
          rw[<- lemma_2_2_2 a]
        conv at h_right =>
          rhs
          rw [exercise_2_2_1 a d k]
        apply prop_2_2_6 at h_right
        symm at h_right
        apply corollary_2_2_9 at h_right
        rcases h_right with ⟨deq,keq⟩
        rw [deq] at h_left
        conv at h_left =>
          rhs
          apply lemma_2_2_2
        contradiction
      .
        by_contra
        rcases this with ⟨ hip_eq, hip_gt⟩
        rw [hip_eq] at hip_gt
        unfold TaoGt at hip_gt
        rcases hip_gt with ⟨ hip_ge, hip_false ⟩
        contradiction




theorem exercise_2_2_4_trichotomy_ver_gemini (a b : TaoNat) : -- Gemini code for the above exercise, asked to use advanced lean features in order to use this as a blueprint for future exercises
    (TaoGt b a ∨ a = b ∨ TaoGt a b) ∧
    (¬(TaoGt b a ∧ a = b)) ∧
    (¬(TaoGt b a ∧ TaoGt a b)) ∧
    (¬(a = b ∧ TaoGt a b)) := by

  -- FEATURE 1: The 'refine' tactic.
  -- Instead of nesting 'constructor' multiple times, 'refine' lets us
  -- split a 4-part AND statement into exactly 4 named goals instantly.
  refine ⟨?existence, ?uniq1, ?uniq2, ?uniq3⟩

  · case existence =>
    induction a with
    | zero =>
      cases b with
      | zero =>
        -- FEATURE 2: Term mode for simple logic.
        -- 'Or.inr (Or.inl rfl)' means "Right door, Left door, Reflexivity" in one line.
        exact Or.inr (Or.inl rfl)
      | succ d =>
        left
        -- 'exact ⟨witness, proof⟩' builds AND statements without 'constructor'
        exact ⟨⟨d.succ, rfl⟩, fun h => by apply axiom_2_3 at h; contradiction⟩

    | succ a ih =>
      rcases ih with h_gt | h_eq | h_lt

      · -- Timeline 1: b > a
        rw [exercise_2_2_3_succ_iff] at h_gt
        -- FEATURE 3: 'obtain' replaces 'unfold' and 'rcases' in one swift move.
        obtain ⟨k, h_ge⟩ := h_gt
        cases k with
        | zero =>
          right; left
          rw [lemma_2_2_2] at h_ge
          exact h_ge.symm
        | succ d =>
          left
          -- FEATURE 4: Semicolons chain tactics on a single line
          exact ⟨⟨d.succ, h_ge⟩, fun h => by rw [h] at h_ge; nth_rw 1 [← lemma_2_2_2 a.succ] at h_ge; apply prop_2_2_6 at h_ge; exact axiom_2_3 d h_ge.symm⟩
      · -- Timeline 2: a = b
        right; right
        exact ⟨⟨zero.succ, by rw [h_eq]; sorry⟩, fun h => sorry⟩ -- Add your lemma chains here

      · -- Timeline 3: a > b
        right; right
        obtain ⟨⟨k, hk⟩, hk_neq⟩ := h_lt
        -- If a > b, then a = b + k. Thus a.succ = b + k.succ. No 'cases k' needed!
        exact ⟨⟨k.succ, by sorry⟩, fun h => sorry⟩

  · case uniq1 =>
    -- Give the inequality a name (h_neq) instead of using the '_' blank
    rintro ⟨⟨_h_ge, h_neq⟩, heq⟩

    -- Lean sees a = b and b ≠ a, but wants them to match perfectly.
    -- Flip a = b into b = a
    symm at heq

    -- Now h_neq (b ≠ a) and heq (b = a) are a perfect clash!
    contradiction

  · case uniq2 =>
    rintro ⟨⟨⟨d, hd⟩, _⟩, ⟨⟨k, hk⟩, _⟩⟩
    rw [hd] at hk
    conv at hk => lhs; rw [← lemma_2_2_2 a]
    conv at hk => rhs; rw [exercise_2_2_1 a d k]
    apply prop_2_2_6 at hk
    -- Flip it first!
    symm at hk

    -- Then apply the corollary!
    apply corollary_2_2_9 at hk

    obtain ⟨deq, keq⟩ := hk
    -- Use 'obtain' to instantly extract the two zero proofs
    rw [deq] at hd
    conv at hd =>
      rhs
      apply lemma_2_2_2
    contradiction

  · case uniq3 =>
    rintro ⟨heq, ⟨⟨k, hk⟩, _⟩⟩
    rw [heq] at hk
    contradiction

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
    let Q (n : TaoNat) : Prop := ∀ x : TaoNat, ( TaoGe x m0 ∧ TaoGt n x) → P x
    have hQ : ∀ n : TaoNat, Q n := by
      intro n
      induction n with
      | zero =>
        rintro x ⟨_, ⟨⟨b, hb⟩, h_neq⟩⟩
        obtain ⟨hx, _⟩ := corollary_2_2_9 hb.symm -- Lean Magic, but very unreadable (proves that x<0 is impossible)
        rw [hx] at h_neq
        contradiction

      | succ k ih =>
          rintro x ⟨⟨⟨a, ha⟩, ha_neq⟩, ⟨⟨b, hb⟩, hb_neq⟩⟩
          apply ih
          unfold TaoGt TaoGe
          exact ⟨⟨a, ha⟩, by
            cases b with
              | zero =>
                rw [lemma_2_2_2] at hb
                contradiction
              | succ d =>
                constructor

                ·
                  use d
                  rw [lemma_2_2_3] at hb

                  apply  at hb

                  exact hb
                ·
                  by_contra
                  rw [this,<-lemma_2_2_2 x.succ] at hb
                  conv at hb =>
                    rhs
                    rw [lemma_2_2_3, prop_2_2_4,<- lemma_2_2_3,prop_2_2_4]
                  symm at hb
                  apply prop_2_2_6 at hb
                  apply  axiom_2_3 at hb
                  contradiction
          ⟩


    intro m hm

    sorry


end RealAnalysis.Tao.Analysis1.Ch02
