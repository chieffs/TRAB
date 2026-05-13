import RealAnalysis.Tao.Analysis1.Chapter02.Axioms
import Mathlib.Tactic

/-!
### Chapter 2 — lemmas and propositions proved from axioms + earlier results only

No `Mathlib.Data.*` imports. Proofs use induction / cases / `rw` with lemmas
from `Axioms.lean` or earlier in this file.
-/

namespace RealAnalysis.Tao.Analysis1.Ch02

open TaoNat (zero succ)

/-- Tao Lemma 2.2.2: `n + 0 = n` (spelled with `zero` so `rw` matches `… + zero`). -/
lemma lemma_2_2_2 (n : TaoNat) : n + zero = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [succ_add, ih]

/-- Tao Lemma 2.2.3: `n + (m++) = (n + m)++`. -/
lemma lemma_2_2_3 (n m : TaoNat) : n + succ m = succ (n + m) := by
  induction n with
  | zero => rw [zero_add, zero_add]
  | succ n ih => rw [succ_add, ih, succ_add]

/-- Tao Proposition 2.2.4: addition is commutative. -/
theorem prop_2_2_4 (n m : TaoNat) : n + m = m + n := by
  induction n with
  | zero => rw [zero_add, lemma_2_2_2]
  | succ n ih => rw [succ_add, ih, ← lemma_2_2_3 m n]

/-- Tao Proposition 2.2.6: left cancellation for addition. -/
theorem prop_2_2_6 {a b c : TaoNat} (h : a + b = a + c) : b = c := by
  induction a with
  | zero =>
    rw [zero_add, zero_add] at h
    exact h
  | succ a ih =>
    rw [succ_add, succ_add] at h
    exact ih (axiom_2_4 h)

/-- Tao Proposition 2.2.8: `a` positive implies `a + b` positive. -/
theorem prop_2_2_8 {a b : TaoNat} (ha : TaoPositive a) : TaoPositive (a + b) := by
  rw [TaoPositive] at ha ⊢
  induction b with
  | zero =>
    intro hab
    rw [lemma_2_2_2] at hab
    exact ha hab
  | succ b _ =>
    intro h
    rw [lemma_2_2_3] at h
    cases h

/-- Tao Corollary 2.2.9: if `a + b = 0` then `a = 0` and `b = 0`. -/
theorem corollary_2_2_9 {a b : TaoNat} (h : a + b = 0) : a = 0 ∧ b = 0 := by
  cases a with
  | zero =>
    rw [zero_add] at h
    exact ⟨rfl, h⟩
  | succ a =>
    rw [succ_add] at h
    cases h

end RealAnalysis.Tao.Analysis1.Ch02
