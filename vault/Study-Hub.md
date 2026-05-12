# Real analysis (Tao) — study hub

Open the folder **`vault`** as your Obsidian vault (or open the parent folder and set `vault` as the only vault root if you prefer a tighter scope).

## Map of content

- **Book notes:** `book/tao-analysis-1/`
- **Lean code:** sibling folder `../lean/` (link from notes using absolute path or `file://` if you like)
- **Templates:** `templates/`

## Rhythm (immersive loop)

1. Read the chapter in the book.
2. Create or update the chapter note from `templates/Tao-Chapter-Note.md`.
3. In Lean, work under `lean/RealAnalysis/Tao/Analysis1/` — either a chapter folder (`Chapter02/Axioms.lean`, …; **4th ed.** uses Ch. 2 for natural numbers) or a single chapter file, depending on how you structured that chapter.
4. Run `lake build` in `lean/` until the chapter file is green.
5. Back in Obsidian, link to the Lean file path and jot what Mathlib tactics or definitions you used.

## Tags (suggested)

`#tao` `#analysis-1` `#ch02` `#exercise` `#definition` `#proof-idea`
