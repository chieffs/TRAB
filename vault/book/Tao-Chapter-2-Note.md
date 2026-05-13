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
### 2.1
0 is a natural number

### 2.2
if n is a natural number, then n++ is also a natural number

### 2.3
0 is note the successor of any natural number; *i.e*, 
$$
\forall n \in \mathbb{N},\, n++ \neq 0
$$
### 2.4
Different natural numbers must have different successors;  *i.e*, if $n,m$ are natural numbers and $n\neq m$, then $n++\neq m++$; Equivalently, if $n++=m++$, then, we must have $n=m$

### 2.5
This axiom is called the principle of mathematical induction.
Let $P(n)$ be any property pertaining to a natural number $n$. Suppose that $P(0)$ is true, and suppose that whenever $P(n)$ is true, $P(n++)$ is also true. Then $P(n)$ is true for every natural number $n.

## Key definitions
### Increment operator (++)
We define the increment operator ++ as such, assuming that 0 exists, as in axiom [[#2.2]]
$0++$ is the successor of 0 and $(0++)++$ is the successor of $0++$, so on and so forth, for every natural $n, \, n++$ is the successor of $n$

### 2.1.3
Numbers.
We define 1 to be the number $0++$, 2 to be the number $(0++)++$,  3 to be the number $((0++)++)++$ and so on and so forth.
### 2.1.1
Natural numbers.
The natural numbers are defined as the set
$$
\mathbb{N} \coloneqq \{ 0,0++,(0++)++,\dots \}   = \ \{ 0,1,2,3,\dots \}
$$
### 2.2.1
Addition.
This is the definition of addition in the natural numbers.
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
2+1 = 3
$$

### 2.2.7
Positive natural numbers.
A natural number $n$ is said to be positive iff (if and only if) it is not equal to 0.
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

### Proposition 2.2.4
Addition is commutative.
For any natural numbers $m,n$ we have $n+m=m+n$
#### Proof
We shall use induction on $n$.
For $n=0$ we have, $0+m=m$ and $m+0=m$ by [[#Lemma 2.2.2]].
Lets assume inductively that this is true for $n$,
so $n+m=m+n$ for $n$.
Now we must prove that $(n++)+m = m + (n++)$.
We know by the [[#2.2.1|definition of addition]] that $(n++)+m=(n+m)++$. We also have, by [[#Lemma 2.2.3]] that $m + (n++)=(n+m)++$. Thus we have reached
$$
(n++)+m = (n+m)++ = m + (n++)
$$
and concluded the induction loop, proving that addition is in fact commutative.

### Proposition 2.2.5
Addition is associative.
For any natural numbers $a,b,c$, we have $(a+b)+c = a+(b+c)$

#### Proof
This proof is actually the exercise 2.2.1 and thus will be proved in the lean exercises part.
Given two arbitrary natural numbers, $b,c$, lets prove inductively that $(a+b)+c = a+(b+c)$, inducting on $a$.
For the base case we have $(0+b)+c = b + c$ and $0+(b+c) = (b+c)=b+c$. 
Then, lets assume that we have a number $n$ such that $(n+b)+c=n+(b+c)$.
Lets prove that $((n++)+b)+c=(n++)+(b+c)$.
From the left hand side we have
$$
((n++)+b) + c = ((n+b)++) + c = ((n+b)+c)++ = (n+(b+c))++
$$
this is true from the [[#2.2.1|addition]] definition and the inductive hypothesis.
From the hand side we have, from the definition of addition
$$
(n++)+(b+c) = (n+(b+c))++
$$

Thus we have reached at the same term from both sides and proved that addition is in fact associative

### Proposition 2.2.6
Cancelation Law.
Let $a,b,c$ be natural numbers such that $a+b=a+c$. Then we have $b=c$

#### Proof
We will prove this by inducting on $a$.
First consider the base case $0+b=0+c$, this case is trivial as $0+b=b$ and $0+c=c$ then $b=c$.
Lets assume inductively we have a case $a$ such that $a+b=a+c$ implies $b=c$.
So we will try to prove that $(a++)+b=(a++)+c \implies b=c$.
By the definition of [[#2.2.1|addition]] we have that:
$$
(a++)+b=(a+b)++
$$
and
$$
(a++)+c=(a+c)++
$$
Lastly, by axiom [[#2.4]] we have that if $n++=m++$ then $n=m$.
so we have that if $(a++)+b=(a++)+c$ we have $(a+b)++=(a+c)++$ and this implies that $a+b=a+c$, by our inductive hypothesis this means that $b=c$, and thus closing the loop and proving the cancelation law.


## Exercises checklist

| # | statement (short) | Lean status |
|---|-------------------|-------------|
| | | todo / sorry / done |

## Lean log

- Module: `lean/...`
- Mathlib highlights:

## Questions / follow-ups
