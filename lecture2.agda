module lecture2 where

{-
Lecture 2
=========

Instead of presenting some research you can develop a small
program/library in Agda and present that.

Deadline is 14/9

^c^n - "normalize" eg. evalutate or simplify
With dependently typed languages you need to normalize the types before it is clear
that the program type-checks. 

'Set' is the class of small types, most normal data is a small
type. Compared to depentent types.


-}

open import Data.Bool

-- data Bool : Set where
  -- true : Bool
  -- false : Bool

-- not : Bool → Bool
-- not true = false
-- not false = true

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

one = succ zero
two = succ one

_+_ : Nat → Nat → Nat
m + zero = m
m + succ n = succ (n + m)

_*_ : Nat → Nat → Nat
m * zero = zero
m * succ n = m + (m * n)

{-
Use the machine numbers.
When normalizing Agda uses the given definitions and not the machine instructions.
-}

{-# BUILTIN NATURAL Nat #-}
zerodecimal : Nat
zerodecimal = 0
--{-# BUILTIN NATPLUS _+_ #-}
--{-# BUILTIN NATTIMES _*_ #-}

{-
Agda has two properties, all programs terminate and dependent types.

Use the pragma: {-# NO_TERMINATION_CHECK #-}

Curry-Howard correspondence: Proposition as types, proofs as programs.

Non-trminating programs dosen't correspond to proofs.

Agda is not sufficiently smart that it always correctly regognises
terminating definitions.

Without termination checking you get a general recursive language.

Dependent types for polymorphic functions
-----------------------------------------
The core of Agda is lambda calculus with dependent tyeps, often called the "Logical
Framwork" or LF.
One type is "Set"
Other are dependent types:
(x:A) → B[x]
Ex: (x:Nat) → Vect Nat x

Set is not a member of itself, that would lead to a contradiction. (Russel)

### Polymorphism
-}

I : (X : Set) → X → X
I X x = x

{- This is more explicit then Haskell which just uses λ x → x, which means ∀a a → a

Agda has implicit arguments so you don't need to specify the types
every time. It uses {} instead of ().  -}

I-impl : { X : Set } → X → X
I-impl x = x
-- I-impl {X} x → x -- You can specify the type anyway if needed.


_○_ : {X Y Z : Set} → (Y → Z) → (X → Y) → X → Z
(g ○ f) x = g (f x)

{-
You don't need anything else except K and S-combinators. (1920) Combinatory logic.
Those two can define every other combinator.

Lists
=====

Data types can be polymorphic too.
-}

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

-- map : {A B : Set} → (A → B) → List B

{- 
Agda is a total language, it does not accept partial functions och incomplete pattern
matching.

The list function head is not a total function.
One solution to this is to introduce a maybe type.

A better solution in Agda is to use depentent types.
Define a head which is only defined on vectors of lenght of at least one.

Dependent types of index data types.
-}

data Vect (A : Set) : Nat → Set where
  [] : Vect A zero
  _::_ : {n : Nat} → A → Vect A n → Vect A (succ n)

head : {A : Set} → {n : Nat} → Vect A (succ n) → A
head (a :: as) = a

{- In some way dependent typing is a compile-time version of quick-check -}

{-

Proving
=======

We use propositions as types.

How do we prove the proposition 1 + 1 = 2
In Agda the formula/propositoin is a type.
We want a type which takes two numbers (small types) and return a type.
It's a data type.

-}

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a
  
{-
Equalities can only be prooved if a thing is equal to itself.
That is what relf means.
-}

1+1=2 : (1 + 1) ≡ 2
1+1=2 = refl

nottrueisfalse : not true ≡ false
nottrueisfalse = refl

notnotid : (b : Bool) → not (not b) ≡ b
{-
This is one of the identifications in Curry-Howard
∀ x : A.P is identified with (x:A) → P[x]

It does not work with just defining notnotid as refl. It is nessescary to pattern match.

Agda does not realize that b is a variable.
-}
notnotid true = refl
notnotid false = refl


-- sym : {A : Set} → (a₁ a₂ : A) → (a₁ ≡ a₂) ‌→ (a₂ ≡ a₁)
-- sym a₁ a₂ p = ?
