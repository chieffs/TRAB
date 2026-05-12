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
Ler $m$ be a natural number. To add 0 to $m$, we define $0+m \coloneqq m$. Now suppose inductively that we have defined how to add $n$ to $m$. Then we can add $n++$ to $m$ by defining
$$
(n++) + m \coloneqq (n+m)++
$$
Thus, $0+m=m$, $1+m=(0++)+m=(0+m)++=m++$.
We will use the shorthand version of addition, by considering $n++ = n+1$ and $n+m$ as a number itself, for example:
$$
2 + 1 = ((0++)++) + (0++) = (0++) +(0++))++ =(((0+0)++)++)++=((0++)++)++ = 3
$$
for short
$$
1+2 = 3
$$


## Key lemmas / theorems

### Lemma 2.2.2
For any natural number $n,n+0=n$.
We cannot deduce this by the definition immediately, as we have not proved the commutative property of the addition.

#### Proof
Using induction, the base case $0+0=0$ is trivial as, $0+m =m$ for any natural number $m$, in this case $m=0$.
Then, lets assume inductively that $n+0=n$, then
$$
(n++) + 0 = (n+0)++=(n)++ = n++
$$
thus we have closed the induction and proved $0+n=n+0=n$

### Lemma 2.2.3
For any natural numbers $n,m$, $n+(m++)=(n+m)++$.
#### Proof
Inducting on $n$ and keeping m fixed we have,
$0+(m++) = m++$ which is exactly the same as $(0+m)++=m++$.
Lets suppose inductively that $n+(m++)=(n+m)++$ , then we will have:
$(n++)+(m++) = (n+(m++))++$, from the inductive hypothesis we have that
$n+(m++)=(n+m)++$, so, $(n+(m++))++=((n+m)++)++$
Now, we only have to prove that $((n++)+m)++=((n+m)++)++$, which is easy, as the definition of addition shows us that $(n++)+m=(n+m)++$, so
$$
((n++)+m)++ = ((n+m)++)++ = (n++)+ (m++)
$$
thus we have closed the induction loop and proved that $n+(m++)=(n+m)++$



## Proof ideas (informal)

## Exercises checklist

| # | statement (short) | Lean status |
|---|-------------------|-------------|
| | | todo / sorry / done |

## Lean log

- Module: `lean/...`
- Mathlib highlights:

## Questions / follow-ups
