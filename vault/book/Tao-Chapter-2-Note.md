---
book: Tao — Analysis I
edition: 4th
chapter: "2"
chapter_slug: natural-numbers
tags:
  - tao
  - analysis-1
lean_file: lean/RealAnalysis/Tao/Analysis1/Chapter02/Basic.lean
date: 12/05/2026
---

# Ch. 2 — Natural numbers

## Summary (own words)
Definition of the natural numbers from the Peano axioms and the properties that follow (Tao Ch. 2, 4th ed.).
## Axioms
### 2.1
0 is a natural number
### Increment operator (++)
We assume there is an operation called the "successor". We will denote the successor of any number $n$  as  $n++$
### 2.2
if n is a natural number, then n++ is also a natural number

### 2.3
0 is not the successor of any natural number; *i.e*, 
$$
\forall n \in \mathbb{N},\, n++ \neq 0
$$
### 2.4
Different natural numbers must have different successors;  *i.e*, if $n,m$ are natural numbers and $n\neq m$, then $n++\neq m++$; Equivalently, if $n++=m++$, then, we must have $n=m$

### 2.5
This axiom is called the principle of mathematical induction.
Let $P(n)$ be any property pertaining to a natural number $n$. Suppose that $P(0)$ is true, and suppose that whenever $P(n)$ is true, $P(n++)$ is also true. Then $P(n)$ is true for every natural number $n.

## Key definitions

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

### 2.2.11
Ordering of the natural numbers.
Let $n,m$ be natural numbers. We say that $n$ is greater than or equal to $m$, and write $n\geq m$ or $m\leq n$, iff we have $n=m+a$ for a natural number $a$. 
We say that $n$ is strictly greater than $m$, and write $n>m$ or $m<n$, iff $n\geq m$ and $n\neq m$

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
Cancellation Law.
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
so we have that if $(a++)+b=(a++)+c$ we have $(a+b)++=(a+c)++$ and this implies that $a+b=a+c$, by our inductive hypothesis this means that $b=c$, and thus closing the loop and proving the cancellation law.


### Proposition 2.2.8
If $a$ is a positive natural number and b is a natural number than $a+b$ is a positive natural number.

#### Proof
We use induction on $b$.
If $b=0$ then we have $a+0=a$ and $a$ is a positive number.
Lets say that $a+b$ is positive for an arbitrary $b$, then we have
$a+b++=(a+b)++$ , using axiom [[#2.3]] we know that if $(a+b)$ is a natural number $(a+b)++\neq 0$, because $0$ is not the successor for any natural number. Thus, we have proved that $a+(b++)$ is in fact positive.

### Corollary 2.2.9
If a and b are natural numbers such that $a+b=0$ then $a=0$ and $b=0$
#### Proof
Lets suppose, for the sake of contradiction, that $a\neq 0$, then we would have 
$a+b=0$ and $a$ is a positive number, but we just proved that if $a\neq 0$ $a+b$ is positive, therefore $a$ cannot be a positive natural. The same reasoning goes for $b\neq 0$ or $a,b\neq 0$.

### Lemma 2.2.10
Let $a$ be a positive number. than exists exactly one natural number such that $b++=a$
#### Proof
This proof is the exercise 2.2.2 and will be on lean's exercise folder.
Lets assume that exists two different natural numbers $b,c$ such that $b++=a$ and $c++=a$ with $b\neq c$. This would be a direct contradiction of axiom [[#2.4]], so we would need to have $b=c$.
For the existence of $b$ lets construct it inductively.
Lets construct a property $P(n):$ if $n\neq 0$ then exists $b$ such that $b++=n$.
For the base case $P(0)$ the property is true, as $n\neq 0$ makes is vacuously true.
Lets assume that this is true for $P(n)$, then we have
$P(n++)$, $n++\neq 0$ from axiom [[#2.3]], then we have $b++=n++$ if $b=n$. Thus proving the induction.

### Proposition 2.2.12
Let $a,b,c$ be natural numbers. Then:

1) (Order is reflexive) $a\geq a$  
2) (Order is transitive) if $a\geq b$ and $b\geq c$ then $a\geq c$
3) (Order is anti-symmetric) if $a\geq b$ and $b\leq a$ than $a=b$
4) (Addition preserver order) $a\geq b$ if and only if $a+c\geq b+c$
5) $a<b$ if and oly if $a++ \leq b$
6) $a<b$ if and only if $b=a+d$ for some positive number d
#### Proof
This proof is the exercise 2.2.3

### Proposition 2.2.13
Trichotomy of order for natural numbers.
Let $a,b$ be natural numbers. Then exactly one of the following statements is true:
$$
a<b, \, a=b, \, a>b
$$

#### Proof
This proof is the exercise 2.2.4
### Proposition 2.2.13
Strong principle of induction.
Let $m_{0}$ be a natural number, and let $P(m)$ be a property pertaining to an arbitrary natural number $m$. Suppose that for each $m\geq m_{0}$, we have the following implication: If $P(m')$ is true for all natural numbers $m_{0}\leq m'<m$ then $P(m)$ is also true. (In particular, this means that $P(m_{0})$ is true, since in this case the hypothesis is vacuous.)Then we can conclude that $P(m)$ is true for all natural numbers $m\geq m_{0}$.

#### Proof
This proof is the exercise 2.2.5
## Exercises checklist

| # | statement (short) | Lean status |
|---|-------------------|-------------|
| | | todo / sorry / done |

## Lean log

- **Axioms & definitions:** `lean/RealAnalysis/Tao/Analysis1/Chapter02/Axioms.lean` — Tao 2.1–2.5, `TaoGe` / `TaoGt` / `TaoPositive`, numerals `tao_one` … `tao_three`, bridge lemmas to `≤` / `<`.
- **Book lemmas (proved):** `…/Chapter02/Lemmas.lean` — Lemma 2.2.2, 2.2.3; Propositions 2.2.4, 2.2.6, 2.2.8; Corollary 2.2.9.
- **Your exercises (`sorry`):** `…/Chapter02/Exercises.lean` — 2.2.1–2.2.5 as in the note.
- Import stack for later chapters: `import RealAnalysis.Tao.Analysis1.Chapter02.Basic`.
- Mathlib: built on `ℕ` = Mathlib natural numbers (same rules as Tao).

## Questions / follow-ups
