% Types for Programs and Proofs - DAT350
% Jakob Larsson <jakob@karljakoblarsson.com>
% Lp1 2017

Lecture 8
=========

Typed λ-calculus.
-----------------

```
t := x | t t | λ x t
```


### CBN ###

$$
\frac{ t₀ ↦ t₀' }{t₀t₁ ↦ t₀'t₁ } \\
\frac{}{ (λ x t) t₁ ↦ t(x/t₁)} \\
$$

### CBV ###

$$
\frac{ t₀ ↦ t₀' }{t₀t₁ ↦ t₀'t₁ } \\
\frac{t₁ \text{value}}{ (λ x t) t₁ ↦ t(x/t₁)} \\
\frac{ t₁ ↦ t₁'   t₀ \text{value}}{t₀t₁ ↦ t₀t₁' } \\
$$

Both have a closed substitution


We don't have normalization $δ λx x x$  $¬∃v δδ ⇓ v$
If $t$ is a closed term. $∃v^? t ⇓ v$ is then undecidable.

### CBN cersus CBV ###
We may have $t ⇓_{CBN} v$ and $¬∃v  t ⇓_{CBV} v$

$t = (λx λy y) (δδ)$ then $t ⇓_{CBV} λy y$ 

Why is CBN not optimal $(λx … x … x …)t$. The computation of $t$ is
difficult.

CBV evaluates $t ⇓ v$ one time. CBN vill do this evaluation many times.

We also have Call-by-Need which is used in Haskell where we try to
"share" the evaluation. Launchbury

_Theorem:_ $t ↦* v ↔  t ⇓ v$

_Start of Proof:_
$t ↦* v ← t ⇓ v$ by induction on $t ⇓ v$.

$v ⇓ v$, $t = v$, $v ↦* v$ and $↦*$ is reflexive.


_Case 2:_
$t ↦* v → t ⇓ v$

_Lemma:_
If $t ↦ t'$ and $t' ⇓ v$ then $t ⇓ v$


This means that small-step semantics is equvivalent to big-step
semantics.

Substitution is really hard to define, the problem is to describe
free and bound variables.


### Nameless representation of terms ###

de Bruijn introduces a nameless representation of terms. (Chapter 5)

```
t ::= n | t t | λ t
n ::= 0 | n + 1


Ex:
λx  (λz  x z) x

Both x refer to the binding in the first lambda. The z is bound in the
second lambda

λ (λ 1 0) 0
```
In this notation the x is represented by both 0 and 1, and one 0
represents z. The numbering is based on the scope. This maps a name
representation to a nameless representation. The algorithm starts with
an empty list of variables and reads the names and translates those to
a nameless representation.

```
translate t xs → nameless term

tz (t₀ t₁) xs    =    (tz t₀ xs) (tz t₁ xs)
tz (λx t) xs     =    (λ  tz  t  (x :: xs)
tz x (z :: xs)   =    0   if x == z
tz x (z :: xs)   =    1 + tz x xs   if x ≠ z
tz x []          =    error(x ++ " is not declared")
```

#### Closures ####
Landin (1964) For CBV
Later Krivine (1985) discoveredan elegant way to do closures for CBN.

```
t ::= n | t t | λ t

closures    cl ::= t, r
environment ρ ::= () | ρ , d
value       v ::= λt, ρ
```

##### Krivine Abstract machine
```
Code    Env    Stack
t     |  ρ  |    S   ↦   t'  | ρ' | S'

λt    | ρ | ()        ↦
λt    | ρ | S.cl      ↦   t  | (ρ, cl) | S
t₀ t₁ | ρ | S         ↦   t₀ | ρ | S.(t₁, ρ)
0     | (ρ,(t,v)) | S ↦ t | v | S
n + 1 | (ρ, cl) | S   ↦ n | ρ | S

```

This abstract machine uses no substitution. This algoritm is a
complete description of the computation. This was not a simple result
to get to but the evalation rules are simple.


#### A mechanical ecaluation of expressions (1964) ####
```
d ::= (t, ρ) | d d
ρ ::= () | ρ, d
v ::= (λt, ρ)


```

$$d ↦ cl'$$

$$
\frac{d0 ↦ d0'}{d0 d1 ↦ d0' d1}
$$

$$
\frac{}{(λt, ρ) d1 ↦ t (ρ, cl1)}
$$

$$
\frac{}{(t0 t1, ρ) ↦ (t0, ρ) (t1, ρ)}
$$

$$
\frac{}{(0, (ρ, cl)) ↦ cl}
$$

$$
\frac{}{(n + 1, (ρ, cl)) ↦ (n, ρ)}
$$

This does not cover Β-conversion or Β-reduction because those
definitions are a bit "informal" but they work. Barendregt wrote about
themin his big book on λ-calculus.

### Β-reduction ###

$$
→_Β   \\frac{}{(λx t)t₁ ↦_Β t(x/t₁)}
$$

$$
\frac{t →_Β t' }{ t t₁ →_Β t' t₁}
$$

$$
\frac{t₁ →_Β t₁' }{ t t₁ →_Β t t₁'}
$$

_Theorem:_ $→_Β$ is confluent.

### Β-conversion ###

$$ Y = λf (λx f(x x)) (λx f(x x)) $$

$Y t =_Β t (Y t)$

This is the Y-combinator which finds the fix-point of any
function. This is a remarkable result of λ-calc, in analysis for ex it
is often hard to find fix-points.

In λ-calculus we can encode Booleans and Natural numbers.

### Denotational Semantics ###

What is the meaning of a λ-term?

Dana Scott.

$$t =_Β t'  →  ⟦ t ⟧ = ⟦ t' ⟧$$


Simply Typed λ-calculus
-----------------------

(Chapter 9, but that presentation is not 100% correct. The one in
Software foundations Vol. 2 is.)

Defined by Church (1940). It inspires ML and Haskell as programming
languages and the HOL and Isabelle proof systems.

```
T, A, B, … ::= Bool | T → T

t ::= true | false | x | t t | λ (x : A) t  -- With names
                   | n | t t | λ A t  -- Namefree

bV ::= true | false
fV ::= λ(x : A) t
```

### CBN ###
Only for _closed_ forms.

$$ \frac{t0 ↦ t0'}{ t0 t1 ↦ t0' t1 } $$

$$ \frac{}{ (λ(x : A) t) t₁ ↦ (x/t₁)} $$


### Type System ###

$t : A$, $\frac{}{true : Bool}   \frac{}{false : Bool}$

$$
\frac{ t₀ : A → B  t₁ : A }{t₀ t₁ : B}
$$

$$
\frac{(x : A) ⊢ t : B}{⊢ λ(x : A) t : A → B }
$$

We need a context which remembers the types of declared variables. The
notation which is used for context is, Γ, Δ, ….

We need an empty context "no declaration". And an update of context
$Γ, x : A$

A context is a partial function from Variables to types `Var → Maybe
Type` The empty context is a function which is never defined.
```
(Γ, x : A)(y) = if x == y then A else Γ(y)
```

A typing judgement is of the form `Γ ⊢ t : A` in the context `Γ t` has
type `A`.

```
Γ(x) defined Γ(x) = A
---------------------
      Γ ⊢ x : A

   γ x : a ⊢ t : b
----------------------
γ ⊢ λ(x : a) t : a → b

Γ ⊢ t₀ : A → B    Γ ⊢ t₁ : A
----------------------------
       Γ ⊢ t₀ t₁ : B
```

Namefree presentation:
```
Γ ::= () | Γ . A


-------------
Γ . A ⊢ 0 : A

   Γ ⊢ n : A
---------------
Γ B ⊢ n + 1 : A

 Γ . A ⊢ t : B
----------------
Γ ⊢ λ At : A → B

Γ ⊢ t₀ : A → B    Γ ⊢ t₁ : A
----------------------------
       Γ ⊢ t₀ t₁ : B
```

Church showed that you can represent ∃ and ∀ as constants in simply
typed λ-calculus. This is used in the HOL proof system.
