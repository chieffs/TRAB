import Mathlib.Tactic

/-!
### Axiomatic layer (Tao *Analysis I*, **4th ed. — Chapter 2**: natural numbers)

**Purpose.** Primitive types, definitions that depend only on earlier chapters,
and **axioms** (or bundled assumptions — see README) that you treat as given
for this chapter.

**Rules of thumb.**

- Nothing in this file should `import` the chapter’s `Exercises` (avoid cycles).
- If something is provable from weaker assumptions, prefer putting the
  *statement* here as a `theorem` with `sorry` **in this same file**, or move it
  to `Lemmas.lean` and only keep the genuine primitives here.

Replace the toy items below with your book-aligned axioms.
-/

namespace RealAnalysis.Tao.Analysis1.Ch02

/-- Toy axiom: replace with real Chapter 2 primitives (natural numbers). -/
axiom toy_neutral : Prop

axiom toy_neutral_true : toy_neutral

end RealAnalysis.Tao.Analysis1.Ch02
