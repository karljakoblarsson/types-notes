module lecture3 where

{-

Lecture 3
=========

What does it mean for subtraction to be correct? It's the inverse of
addition. How do we prove this in Agda?

QuickCheck is a simple way to specifiy properties of programs. It can
only specify a subset of the things you can prove in Agda.

Last week we looked at simply typed Agda. Only ordinary function
space, and not dependent type. Last lecture we looked at polymorphic
functions and data types, and inductive families, or dependent
datatypes like vectors, they are approx gadt in Haskell. And a small
amount of proving with Curry-Howard. I.e. that propositions are
represented as sets/types and proofs are represented as programs.

We introduced a proof object refl which represented an equality.

-}

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

{-

Proof by Induction on Nat
-------------------------

It will be similar to boolean proofs and will use pattern
matching. But we need to use primitive recursion.

^c^s - solve goal automatically

cong is proving a congruence.

-}

cong : {A B : Set} → {a₁ a₂ : A} → (f : A → B)
  → a₁ ≡ a₂
  → f a₁ ≡ f a₂
cong f refl = refl

open import Nat

assoc-plus : (m n p : Nat) → (m + n) + p ≡ m + (n + p)
assoc-plus m n zero = refl
assoc-plus m n (succ p) = cong succ (assoc-plus m n p)

{-
To use proofs as programs we can't use the law of excluded middle. And not ¬¬A →A


We can prove the general priciple of induction of the natural numbers
using propositions as types. This is analougus to using higher-order
functions when programming functionally
-}

natind : {P : Nat → Set}
  → P zero
  → ((m : Nat) → P m → P (succ m))
  → (n : Nat) → P n
natind base step zero = base
natind base step (succ n) = step n (natind base step n)

assoc-plus-ind : (m n p : Nat)
  → ((m + n) + p) ≡ (m + (n + p))
assoc-plus-ind m n p
  = natind {λ p → ((m + n) + p) ≡ (m + (n + p))}
           refl
           ((λ p r → cong succ r))
           p

{-

Propositional Logic
-------------------

Curry (1930s) second inventor of combinatory logic after Church and
his lambda calculus. The beginnings of functional programming.

The identity combinator:
-}

I : {A : Set} → A → A
I x = x

{-
The composition combinator:
-}

-- B :

K : { A B : Set} → A → B → A
K = {!!}

{- Curry notices the similarity between the formulas and the types for
propositional logic. But he didn't build on it. Then Howard (1960s)
used propositional types for predicate logic by introducing dependent
types.

prop  | types
-------------
A ⊃ B | A → B
A ∧ B | A × B
A ∨ B | A + B (disjoint union)

-}
