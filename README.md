# TRAB

Short for **T**ao **R**eal **A**nalysis **B**ook (in **Lean**): a study workspace for Terence Tao’s *Analysis I* (and later *Analysis II*). Use **Obsidian** for chapter notes and intuition, and **Lean 4** with **Mathlib** to formalize definitions, proofs, and exercises.

**Edition note:** folder names such as `Chapter02` follow **Tao *Analysis I*, 4th edition** chapter numbering (for example **natural numbers = Chapter 2**). If you use another edition, renumber Lean paths and notes to match your book.

**Remote:** [github.com/chieffs/Trab](https://github.com/chieffs/Trab)

**Who am I and goals for this project:**

I have a degree in applied maths and am currently conducting research in epidemiology and causal inference. This project is my way of learning Lean 4 and Real Analysis concurrently. All the Obsidian notes are my notes and paraphrasing from the book *Analysis* by Terence Tao.
I use Cursor AI to help maintain the repository and—**only for lemmas and corollaries that the book proves in full (not as exercises)**—sometimes to write the **Lean** formalization. **I write all Lean for exercises myself.** **All** lemma text in my notes (including in Obsidian) and **all LaTeX** are mine; Cursor may assist **only** with that book-proved, non-exercise Lean.
Also every error in this project is solely my own fault and not the fault of Cursor or Tao's work.
I hope you have a nice time or learn something from this repository, as I certainly had both a great time and a great deal of learning from this.


Clone:

```bash
git clone https://github.com/chieffs/Trab.git
cd Trab
```

## Prerequisites

- [Elan](https://github.com/leanprover/elan) (Lean toolchain manager) and a working `lake` command.
- [Obsidian](https://obsidian.md/) (optional but recommended for notes).
- A local clone of this repository.

## Repository layout

```text
.
├── LICENSE                   # MIT
├── README.md                 # This file
├── lean/                     # Lean 4 Lake project (Mathlib)
│   ├── lakefile.lean
│   ├── lean-toolchain        # Pin aligned with Mathlib
│   ├── RealAnalysis.lean     # Library root: import chapter *Basic* modules here
│   └── RealAnalysis/
│       └── Tao/
│           └── Analysis1/
│               └── Chapter02/   # 4th ed.: natural numbers (see Layered chapters)
│                   ├── Axioms.lean
│                   ├── Lemmas.lean
│                   ├── Exercises.lean
│                   └── Basic.lean    # re-exports stack for downstream imports
└── vault/                    # Obsidian vault root
    ├── Study-Hub.md          # Entry point and quick workflow
    ├── templates/
    │   └── Tao-Chapter-Note.md
    └── book/
        └── tao-analysis-1/   # Chapter notes live here
```

If you add *Analysis II*, mirror the pattern: `lean/RealAnalysis/Tao/Analysis2/` and `vault/book/tao-analysis-2/`.

## Layered chapters

Lean has two constraints worth designing around:

1. **A `theorem` / `lemma` must be finished in the same file** (you cannot put
   `theorem T : P := by sorry` in `Axioms.lean` and complete the proof in
   `Exercises.lean` under the same name `T`).
2. **An `axiom` cannot later be “proven” in another file** as the same
   declaration. If you want a track where exercises *derive* what the book
   treats as primitive, use one of the patterns below instead of a global
   `axiom` you intend to delete.

### Recommended layout per chapter

Use a **folder** under `Analysis1/` (example: `Chapter02/` for natural numbers in the 4th ed.):

| File | Role |
|------|------|
| `Axioms.lean` | Primitive notions + **axioms** (or a bundled `structure` whose fields are the assumptions you want to discharge later). |
| `Lemmas.lean` | Imports `Axioms`. Proves lemmas using only that layer (Chapter 2 uses **no** `Mathlib.Data.*` — only `Mathlib.Tactic`). |
| `Exercises.lean` | Imports `Lemmas`. Book exercises; may use axioms and lemmas. |
| `Basic.lean` | Imports the three files above **in order** so other chapters can `import …Chapter02.Basic` once. |

**Dependency direction:** `Axioms` ← `Lemmas` ← `Exercises` ← `Basic`. Never import `Exercises` from `Axioms` or `Lemmas`.

**Later chapters** should import `Chapter02.Basic` (or a curated `Chapter02/Index.lean` if you grow many files), not individual exercise files, unless you want a minimal dependency surface.

### If exercises should “prove the axioms”

Pick one strategy:

- **Bundled assumptions (often best for coursework).** In `Axioms.lean`, define  
  `structure Chapter02Assumptions := { field1 : …, field2 : … }`  
  where each field is one of the book’s axioms as a proposition (or data + laws).  
  Exercises then build `def myModel : Chapter02Assumptions := { … }` with proofs
  in `Exercises.lean`, possibly after you’ve proved helper lemmas in `Lemmas.lean`.

- **Two development tracks (minimal vs full).** Keep a **small** `AxiomsTrack`
  (few real `axiom`s) for early chapters; in a separate folder or later module,
  prove **new theorems** with the same *statement* as the book’s principles from
  a weaker basis, then **switch imports** when you are ready to depend on the
  stronger development (Git branches help here).

- **Global `axiom` only for genuinely irreducible steps** you never intend to
  remove (rare in a Mathlib-based course of analysis — usually you instead
  import Mathlib’s already-constructed objects).

### One-file alternative

If a chapter is small, a single `.lean` file with clearly marked sections
(`/- Axioms -/`, `/- Lemmas -/`, `/- Exercises -/`) is fine; the same Lean rules
apply, but you avoid import plumbing.

## How to study from this project

Use a fixed loop so notes and formal code stay aligned.

1. **Read** the assigned section in Tao’s book.
2. **Note** — In Obsidian, open `vault` as your vault. Copy `vault/templates/Tao-Chapter-Note.md` into `vault/book/tao-analysis-1/` with a clear name (for example `ch02-natural-numbers.md` for the 4th ed.). Fill summary, definitions, informal proof ideas, and the exercise checklist table.
3. **Formalize** — In `lean/RealAnalysis/Tao/Analysis1/`, edit the chapter file (or create a new one). State theorems for each exercise; use `sorry` as a scaffold until the proof is complete.
4. **Check** — From `lean/`, run `lake build`. Fix errors until the project builds.
5. **Reflect** — Update the chapter note: exercise statuses, Mathlib lemmas you used, and questions for later.

Optional: use tags such as `#tao`, `#analysis-1`, `#ch02`, `#exercise` in front matter or inline for easier search.

## How to add to the project

### New chapter (Lean), layered style

1. Create a folder `lean/RealAnalysis/Tao/Analysis1/ChapterNN/`.
2. Add `Axioms.lean`, `Lemmas.lean`, `Exercises.lean`, and `Basic.lean` following
   the table in [Layered chapters](#layered-chapters).
3. Add `import RealAnalysis.Tao.Analysis1.ChapterNN.Basic` to `lean/RealAnalysis.lean`.

### New chapter (Lean), single-file style

1. Add one file under `lean/RealAnalysis/Tao/Analysis1/`, for example
   `Chapter04_IntegersRationals.lean`.
2. Use a chapter-scoped namespace (for example `namespace RealAnalysis.Tao.Analysis1.Ch04`) and `import` only the Mathlib modules you need (prefer narrow imports over blanket `import Mathlib` when possible).
3. Open `lean/RealAnalysis.lean` and add a matching `import` line so Lake builds the new module.

### New chapter (Obsidian)

1. Duplicate `vault/templates/Tao-Chapter-Note.md` into `vault/book/tao-analysis-1/`.
2. Set front matter (`chapter`, `chapter_slug`, `lean_file`, `date`) and link to the corresponding path under `lean/RealAnalysis/...`.

### New exercise or lemma

- **Layered folder:** add lemmas to `Lemmas.lean` (if they belong to the lemma
  layer) or to `Exercises.lean` if they are book exercises or exercise-only
  helpers. Keep `Axioms.lean` for primitives and axioms only.
- **Single file:** add a `theorem` or `lemma` with a stable name (for example
  `ex_4_3_7` for Exercise 4.3.7).
- Mark unfinished work with `sorry` in **that same file** until the proof is complete.
- Track status in the chapter note’s exercise table.

### Toolchain and Mathlib

If `lake build` fails because of a Lean or Mathlib version mismatch, align `lean/lean-toolchain` with the version declared in [mathlib4’s `lean-toolchain`](https://github.com/leanprover-community/mathlib4/blob/master/lean-toolchain), then run:

```bash
cd lean
lake update
lake exe cache get   # optional; speeds up Mathlib fetch/build
lake build
```

### Git and GitHub

Commit notes and Lean together so each commit tells a coherent story (for example “Chapter 2 (4th ed.): exercises 2.2.1–2.2.6”).

## License

This repository is licensed under the [MIT License](LICENSE).

Terence Tao’s *Analysis I/II* is not included here (only your notes and Lean sources). Mathlib is a separate dependency under its own license; see [mathlib4](https://github.com/leanprover-community/mathlib4).
