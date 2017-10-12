% Types for Programs and Proofs - DAT350
% Jakob Larsson <jakob@karljakoblarsson.com>
% Lp1 2017

Lecture 9
=========
(Chapter 9 & 12)

Last time we looked at simply typed λ-calculus.

Now Higher Order Logic:

$$
∀x  p(x) = ∀(λ(x : T) p x) = ∀ p \\
∃x   p(x) = ∃p
$$

```Pseudo
∃ : (Nat → Bool) → Bool
∃p = true if there exists an n such that p(n) = true
     false if for all n: p(n) = false
```
$$
∀p = \text{not} (∃ (λ (x : T) \text{not}(p(x)))
$$

```Pseudo
∃ p = if p(0) == true then true else ∃(λ (n : Nat) p (n+1))
```

If `p` is always false the program _loops_.

```
Π : (T → Set) → Set
Π f = ?

-- Π (x : T)(p x) is a type of proof, not a boolean.
-- Everything is computable in Agda.

-- data Σ (x : T) P x
-- ( a , b )  a : T  b : P a
```

```
Types A ::= Bool | A → A

Γ  partial function Var → (Maybe) Types
```
 
$Γ ⊢ t. A$

$\frac{Γ(x) → A}{Γ ⊢ x : A}$
$\frac{Γ ⊢ t. A → B   Γ ⊢ u : A}{ Γ ⊢ t u : B}$
$\frac{Γ x : A ⊢ t. B}{ Γ ⊢ λ(x : A) t. A → B}$

### CBN

$\frac{t₀ ↦ t₀'}{t₀ t₁ ↦ t₀' t₁}$
$\frac{}{ (λ(x : A) t) t₁ ↦ t(x/t₁)}$
`v ::= true | false |  λ(x : A) t`

`Γ ::= ) | Γ . A`
$\frac{Γ ⊢ t A → B   Γ ⊢ u : A}{ Γ ⊢ t u : B}$
$\frac{Γ . A ⊢ t : B}{Γ ⊢ λA t : A → B}$
$\frac{}{Γ . A ⊢ 0 . A}$
$\frac{Γ ⊢ n : A}{Γ . B ⊢ n+1 : A}$

### Closures
```
-- A closure is defined by: 
c ::= t ρ | c c | true | false
ρ :: = ) | ρ, c
v ::= (λ A t) ρ | true | false
```

$\frac{c₀ ↦ c₀'}{c₀ c₁ ↦ c₀' c₁}$
$\frac{}{(λ A:t) ρ c ↦ t( ρ, c)}$
$\frac{}{(t₀ t₁) ρ ↦ (t₀ ρ)(t₁ ρ)}$
$\frac{ \frac{}{O(ρ, c) ↦ c} }{(m+1)( ρ, c) ↦ n ρ}$

This completely defines the evaluation of simply typed λ-calculus
without using any predefined operations like substitution. Which is
nice.

$c : A $
$ρ : Γ$

$\frac{}{() : ()}$

$\frac{ρ : Γ   c : A}{(ρ, c) : Γ . A}$

$\frac{Γ ⊢ t : A  ρ : Γ}{ t ρ : A}$
$\frac{ cₐ : A → B   c₁ . A}{ c₀ c₁ : B}$

$\frac{}{true : Bool}$
$\frac{}{false : Bool}$


### Progress Theorem:
If $c : A$ then $c$ is a value $∨ ∃c'    c ↦ c$.
It's proved by induction.

### Preservation Theorem:
If $c : A$ and $c ↦ c'$ then $c' : A$. 

But we don't know that the computation terminates.

The proof is again by induction.

Substitution is actually really complicated to implement on a
computer, since there are a lot of edge cases. Therefore the
presentation above is good since it does not use substitution.


### Combined Progress and Preservation:
$c : A   c ↦ c'$ then $c' : A$

#### Collary:
If $c : Bool$ and $ c ↦* v$ then $v =$ true or $v =$ false.
The proof uses preservation.

### Normalization Theorem:
If $c : A$ then $∃v   c ↦* v$. (This is proven in Chapter 12.) The
proof uses a technique which is fundamental in software foundations
which is called the method of logical relation or induction on types.

It will not work to do induction on $c : A$. Instead we define a
predicate $R_A(c)$, where $c : A$, by induction on $A$.

$$
R_{Bool}(c)   ∃ v (c ↦* v) \\
R_{A→B}(c)   ∀c₁ : A R_A(c₁) ⇒ R_B(c c₁)
$$

The goal is the show that if $c : A$ then $R_A(c)$ holds.

#### Lemma 1:
If $c : A   c ↦ c'$ and $R_A(c')$ then R_A(c)$.

##### Proof:
By induction __on A__.
If $A =$ Bool and (case 1) $\frac{c ↦ c' ↦* v}{c ↦* v}$
(case 2): $A = B → C  R_{B→ C}(c')$ if $c₁ : B$ and $R_B(c₁)$. No we
now that $R_C(c' c₁)$ and $c  c₁ ↦ c' c₁$ by definition.

```Agda
R : Types → Closure → Set
-- R will be defined recursivly on types
R a b = ?
```

#### Lemma 2:
If $\frac{c : A}{R_A(c)}$

##### Proof:
$$ \frac{Γ ⊢ t : A   R_Γ(ρ)}{R_A(t ρ)} $$

$$ \frac{}{R_{)}()} $$

$$ \frac{R_Γ(ρ)   R_A(c)}{ R_{Γ : A}(ρ, c)} $$

Then using Lemma 1 we have: $\frac{R_{B → A}((t₀ ρ)   R_B(t,
ρ)}{R_A((t₀, ρ) (t, ρ))}$

$(t₀ t₁ ↦ $

And all the other cases are similar.

At this point we know: if $c : $ Bool then $R_{\text{Bool}}(c)$ so
$∃v  c ↦* v$


#### Lemma 3:
If $R_A(c) ⇒ ∃v (c ↦* v)$. We will not prove Lemma 3 but it's
apperantly not complicated. (Hint: for any type $A$ we can find a
special elemet $f_A : A   R_A(f_A)$. Usisng this it should be easy to
proove the lemma.)

In this language we add the negation function `neg : Bool → Bool`.

We can buil `t : Bool` of size $~n$ but when we try to compute it $t
↦* v$ it will take $2^{2^{2^{⋱}}}  n$ times.


This proof is possible and a nice exercise to implement in Agda.

Next time Ulf Norell will talk about implementing simply typed
λ-calculus in Agda.
