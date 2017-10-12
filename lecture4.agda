module lecture4 where

{-

Lecture 4
=========

The correspondence between propositional logic and simple types was discovred bu Curry.
And the basic combinators of lambda-calculus.

Combinators can make programs shorter but patternmatching is often more clear.

The unit type correspondes to a proposition which is unconditionally and trivially true.

-}

data ⊤ : Set where
  <> : ⊤

-- Similary, the empty set corresponds to something which is absrud or
-- trvially true.  But as always. You can not prove absurdity. It also
-- implies everything.

data ⊥ : Set where

-- Similary we can not construct an element of absurdity, unless you
-- start with one.


nocase : {C : Set} → ⊥ → C
nocase ()

-- Where () indicates that it's impossible to instansiate nocase in a
-- type-correct way.

-- A specific imply-introduction
data _⊃_ (A B : Set) : Set where
  ⊃-intro : (A → B) → A ⊃ B

-- Modus pones
mp : {A B : Set} → A ⊃ B → A → B
mp (⊃-intro g) a = g a

¬ : Set → Set
¬ A = A → ⊥

-- With this definiton you can't prove the law of the excluded middle
-- nor dubble negation. This is because every Agda-proof is a
-- computable function. But this proof is not computable.

-- There are exercises in the proplogic.agda file.

{-

Predicate Logic
---------------

To encode predicate logic you need dependent types. Howard had a
dependent type theory on paper. Then de Bruijn started the digital
work.

-}

data ∃ (A : Set) (P : A → Set) : Set where
  <_,_> : (a : A) → P a → ∃ A P

witness : { A : Set} {P : A → Set} → ∃ A P → A
witness < a , p > = a

proof : {A : Set} → {P : A → Set} → (c : ∃ A P) → P (witness c)
proof < a , p > = p

-- data ∀' (A : Set) (P : A → Set)

{-

Reccords
--------

With dependent types you can more with records then simple types.

Records are isomorphic to tuples but with named fields (p1 × p2 × p3 × ⋯)

-}

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Bool
{-# BUILTIN STRING String #-}

record Date : Set where
  field
    year : Nat
    month : String
    day : Nat

today : Date
today = record { year = 2017
               ; month = "September"
               ; day = 11
               }

year-of : Date → Nat
year-of = Date.year


record _x_ (A B : Set) : Set where
  field
    l1 : A
    l2 : B

isTrue : Bool → Set
isTrue true = ⊤
isTrue false = ⊥
                                   
-- Similar to the "Set" interface of Java collections.
record FiniteSubset : Set₁ where
  field
    set : Set -- the implementation data type
    _∈_ : Nat → set → Bool
    size : set → Nat
    empty : set
    insert : Nat → set → set
    -- A property of the datatype.
    insert-∈ : {n : Nat} → {ns : set} → isTrue (n ∈ insert n ns)

-- As seen here you can define properties on the data definitions
-- which are checked when the definition is type-checked.
