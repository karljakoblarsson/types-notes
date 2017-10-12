% Types for Programs and Proofs - DAT350
% Jakob Larsson <jakob@karljakoblarsson.com>
% Lp1 2017


Lecture 4 - Introduction to operational semantics
=================================================

Based on Chapter 3 Pierces book.

The main application is correctness of programs.
The problem is how to specify programs in a mathmatically precise way.

The usual tools i math, e.g. anlysis, are not at all suited to hande
discreet object such as programs.

History
-------

Document, which is important for modularity.
Operational semantics can be represented nicely in interactive theorem provers.

Two different kinds of interactive theorem provers.
Either based on higher order logic, such as: HOL, Isabelle.
Or based on Type theory, such as: Agda, Coq, Idris, Lean.

The difference are that tye theoretic provers represent proofs explicitly.

CompCert by  X. Leroy is a provably coorect C-compiler.
CoteML developed here by M. Myrem a complete and correct ML-language.

How to represent programs
-------------------------

### Arithmetic expressions ###
Are represented as an abstract syntax tree. It maps to a data type in Agda.

Ex: ``` e := const n | add e e | mult e e ```

One of the earliest uses of this representation was Gödel in his
incompletness proof. (1930)

LISP (McCarthy 1958) builds LISP using the idea of an AST.

### In Agda ###
```Agda
-- Nat - the set of natural numbers
exp : Set
const : Nat → exp
add : exp → exp → exp
mult : exp → exp → exp
```

### How to prove an expression ###
Use induction. E.g. to prove $e C(e)$$$
a: ∀n C(const n) \\
b: ∀e₀e₁ C(e₀) → C (e₁) → C(add e₀ e₁) \\
c: ∀e₀e₁ C(e₀) → C (e₁) → C(mult e₀ e₁) \\
$$

$a: (n : Nat) → C(const n)$
$$
f(const n) = a n
f(add e₀ e₁) = b (f e₀) (f e₁)
f(mult e₀ e₁) = c (f e₀) (f e₁)
$$

Define $f$ by pattern-matching and recursion.

Then we prove $C(e)$by induction on$e$.

#### Proof ####
On expressions we can define *functions*, ex:
```Agda
depth : exp → Nat
depth(const n) = 1
depth(add/mult e₀ e₁) = 1 + max(depth e₀, depth e₁)

size : exp → Nat
size(const n) = 1
size(add/mult e₀ e₁) = 1 + size e₀ + size e₁)
```

$∀e depth e ≤ size e$

```Agda
_+_ : Nat → Nat → Nat -- function add constructor
_≤_ : Nat → Nat → Set
max : Nat → Nat → Set
```

### Denotational Semantics ###
Three different kinds of semantics: Operational, Denotational, Axiomatic.
In denotational semantics we try to build "meaning" fo a program, or the "value".
We want to define the function ```val```, in this case: ```val : Exp → Nat```.

We assume the have already defined _+_ and _×_.
```Agda
value (const n) = n
value (add e₀ e₁) = (value e₀) + (value e₁)
value (mult e₀ e₁) = (value e₀) × (value e₁)
```

Denotational semantics are really nice when it's possible to define
the value. However this is often not "possible" or at least very hard.

### Operational semantics ###
How to mathematically represent the evaluation of a program?

$e ↦ e'$ One-step evaluation. A binary relation of expressions
```Agda
_↦_a : exp → exp → Set
```

The left-rule of addition.
$$L_add = \frac{ e₀ ↦ e₀' }{ add e₀ e₁ → add e₀' e₁}$$

The rigth-rule of addition.
$$R_add = \frac{ e₁ ↦ e₁' }{ add (const n) e₁ → add (const n) e₁'}$$

The rigth-rule of addition.
$$D_add = \frac{}{ add (const n) (const m) ↦ const (n+m)}$$


Note that there are no rules for $const n ↦$

There are analougus rules for multiplication.

We can use this to reason about the _cost_ of computation.

The one-step evaluation _↦_ is a relation. It is also a proposition. In Agda:
```Agda
e ↦ e' : Set
```

### Normal form ###
En expression/term is in normal form when it can not be evaluated further.
$e$ normal form  $\textlnot ∃e' e↦e'$

Theorem: $e $ normal form → $ e$ value.

```Agda
isValue : exp → Bool
isValue (const n ) = true
isValue _ = false
```

If $e$is not a value → $ e $ is not in formal form.$ e $not a value → $ ∃e' (e → e')$

PBI: (Proof by induction)

Case by case.

$$(1) e = cont n $$

$C(e) $ is of the form $ ⊥ → …$ hence is it valid.

```Agda
⊥ : Set
⊤ : Set

isValue (const n) = ⊤
isValue _ = ⊥
```
$$(2) e = add eₒ e₁$$

By case $e₀$

It was a long time before people cpuld reason about programs in this
precise way. The problem was to find the right formulation.

## Several steps of evalutation ##
$e ↦* e'$ means that $e$ reduces in several steps to$e'$

A chain for evaluation $↦ e ↦$.

One possible definition
```Agda
_↦*_ : exp → exp → Set
```

Two constructors:

$$\frac{}{ e ↦* e' }$$

$$\frac{ e ↦ e'   e' ↦* e''}{ e ↦* e'' }$$

$↦*$ is called reflexive transitive closure of $↦$. It's a genral
definiton for any given definition of $↦$.

Proposition: if $e ↦* e'$ and $e' ↦* e''$ → $e ↦* e''$.

It is a valid rule (but not by definition). An admissible rule.

This expresses that the relation ↦* is transitive.

Theorem (Normalization): $∀e ∃e' e ↦* e' ∧ e' $ is a value.$ ∀e ∃n e ↦* const n $

```Agda
val : exp Nat
```
$∀e e ↦* const (val e)$

This connects denatitional and operational semantics. The ```val```
function is from denotational semantics and the $↦*$ is from operational.

### By induction on e ###
(This is nice to do in Agda)

- $e = const n $ and $ val e = n $ and the rule $ \frac{}{ e ↦* }$

- $e = add e₀ e₁ $ by IH: $ e₀ ↦* const (val e₀) $  $ e₁ ↦* const (val e₁)$

#### Lemma 1 ####
$$\frac{ e₀ ↦* e₀' } { add e₀ e₁ ↦* add e₀' e₁ }$$

#### Lemma 2 ####
$$\frac{ e₁ ↦* e₁' } { add (const n) e₁ ↦* add (const n) e₁' }$$

- $e ↦* add (const (val e₀)) e₁$
- $↦* add (const (val e₀)) (val e₁)$
- $↦ add (const (val e₀) (val e₁))$


Both lemmas are examples of admissible rules.

Basic rules corresponds to constructors. Admissible rules correspond
to functions.
