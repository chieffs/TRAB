import RealAnalysis.Tao.Analysis1.Chapter02.Axioms

/-!
### Lemmas layer

**Purpose.** Results proved using only `Axioms` (and earlier chapters / Mathlib
imports you allow into the axiomatic track).

Downstream `Exercises` and later chapters may import this file to reuse lemmas
without importing exercise-specific names.
-/

namespace RealAnalysis.Tao.Analysis1.Ch02

lemma toy_neutral_iff_true : toy_neutral ↔ True :=
  ⟨fun _ => trivial, fun _ => toy_neutral_true⟩

end RealAnalysis.Tao.Analysis1.Ch02
