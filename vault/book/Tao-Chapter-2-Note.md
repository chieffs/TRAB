---
book: Tao — Analysis I
edition: 4th
chapter: "2"
chapter_slug: Real Numbers
tags:
  - tao
  - analysis-2
lean_file: Chapter02_NaturalNumbers.lean
date: 12/05/2026
---

# Ch.2 — title

## Summary (own words)
Definition of the real numbers base on Peano Axioms and the properties emerging from them
## Axioms
### 1
0 is a natural number

### 2
if n is a natural number, then n++ is also a natural number

### 3
0 is note the successor of any natural number; *i.e*, 
$$
\forall n \in \mathbb{N},\, n++ \neq 0
$$
### 4
Different natural numbers must have different successors;  *i.e*, if $n,m$ are natural numbers and $n\neq m$, then $n++\neq m++$; Equivalently, if $n++=m++$, then, we must have $n=m$

### 5
This axiom is called the principle of mathematical induction.
Let $P(n)$ be any property pertaining to a natural number $n$. Suppose that $P(0)$ is true, and suppose that whenever $P(n)$ is true, $P(n++)$ is also true. Then $P(n)$ is true for every natural number $n.

## Key definitions
### Increment operator (++)
We define the increment operator ++ as such, assuming that 0 exists, as in axiom [[#2]]
$0++$ is the successor of 0 and $(0++)++$ is the successor of $0++$, so on and so forth, for every natural $n, \, n++$ is the successor of $n$

### Natural numbers
The natural numbers are defined as the set
$$
\mathbb{N} \coloneqq \{ 0,0++,(0++)++,\dots \}   
$$
### Addition
This is the definition of addition to the natural numbers.
Ler $m$ be a natural number. To add 0 to $m$, we define $0+m \coloneqq m$. Now suppose inductively that we have defined how to add $n$ to $m$.
T
## Key lemmas / theorems

## Proof ideas (informal)

## Exercises checklist

| # | statement (short) | Lean status |
|---|-------------------|-------------|
| | | todo / sorry / done |

## Lean log

- Module: `lean/...`
- Mathlib highlights:

## Questions / follow-ups
