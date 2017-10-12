% Lecture 6 - Types for Programs and Proofs - DAT350
% Jakob Larsson <jakob@karljakoblarsson.com>
% Lp1 2017


Typed Arithmethc Expressions
----------------------------

A simple arithmetic language with booleans.
```Pseudo
t ::= true | false | if t t₁ t₂ | 0 | succ t | pred t | isZero t

v ::= bv | nv

bv ::= true | false
nv ::= 0 | succ nc

```

This language has well defined operational semantics. Which I won't
list here
.

### Value ###
is the expected result of a computation.

### Progress ###
$\text{value} t ∨ ∃t'  t ↦ t'$
This is the decidable property of $t$. Which is something you want.

### Soundness ###
$t ↦* t' → ⌉(\text{stuck} t')$
Not decidable in general.

### Type system ###
R. Milner "well-typed programs do not go wrong" (1978)
Implies soundness.


1. $t : T → \text{value} t ∨ ∃t'  t ↦ t'$ _progress_
2. $t : T ∨ t ↦ t'   → t' : T$ _type presentation_

```Pseudo
T ::= Bool | Nat
```

This has valid operational semantics as well.

For a given `T` and `t` we expect `t : T` to be decidable.


Type Soundness
--------------
(Milner's theorem)

$$
t : T
t ↦* t'

both → ⌉(\text{wrong} t')
	t' \text{value}
 ∨ ∃t''   t' ↦ t''
$$

By induction on $t ↦* t'$

- $\frac{}{t ↦* t'}$ by (1) $t \text{value} ∨ ∃t''   t ↦ t''$
- $\frac{t ↦ t₁   t₁ ↦* t'}{t ↦* t'}$, $t :T$ and $t ↦ t₁$ by (2)


Untyped λ-calculus
==================
(Chapters 4 and 5)

```λ-calc
e ::= x | e e | λ x. e

```
`x` is a variable. `e e` is and application. `λ x e` is an abstraction
or λ-abstraction.

It's a general calcullus of __functions__. Alonzo Church (1930)

Normal calculus | λ-calc
:----------------|:--------
$f : x ↦ x² + 1$ | $λx. x² + 1$
$f : y ↦ 2y$ | $λy. 2y$
$id : z ↦ z$ | $λz. z$

$(λx.e)5$


value ∨ $λx.e$

$∃v   e ↦* v$ This was the first
example of a question which can not be decidable by a program.

This notation was used in LISP (1960) as a practical language. Landin
(1964) introduced the closure in A mechanical evaluation of
expressions. The Scheme was designed in 1976.


Call-by-value/Call-by-name
--------------------------

__substitution__ `e(x/e')` substitute `e'` for `x` in `e`. `e'` is
__closed__ if `e'` has no free variables.

`FV(e)` is the set of free variables of `e`
`FV : exp → [identifiers]`

A variable which is not free is called bound.

```Pseudo
FV( x ) = { x }
FV(e₁ e₂) = FV(e₁) ∪ FV(e₂)
FV(λx. e) = FV(e) ∖ { x }

```

It is legal to remane a bound variable but it's not legal to rename a
free variable.


There was a big problems with substitutions of this kind:
$(λz. x)(y/z)$ This changes the function from a constant function to
the identity function. This problem was solved by the introduction of
the closure by Landin (1964).

### CBN ###
Haskell

$$
\frac{e₀ ↦ e₀'}{e₀ e₁ ↦ e₀' e₂}
$$

$$
\frac{}{(λx.e) e₁ ↦ e(x/e₁)}
$$

### CBV ###
ML, OCAML

$$
\frac{e₀ ↦ e₀'}{e₀ e₁ ↦ e₀' e₂}
$$

$$
\frac{e  \text{value}  e₁ ↦ e₁'}{e₀ e₁ ↦ e₀ e₁'}
$$

$$
\frac{e₁  \text{value}}{(λx.e) e₁ ↦ e(x/e₁)}
$$


$∃v (e ↦* v)$ is undecidable both for CBN and CBV. The behavior of
$↦*$ can be very complex.

$$δ = λx. x x$$ This combinator applies a function to itself. This
seems wierd but is ok. $δδ ↦ δδ$, so $δδ$ is not a value. $⌉∃v (δδ ↦* v)$.


