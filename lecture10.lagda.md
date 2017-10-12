% Types for Programs and Proofs - DAT350
% Jakob Larsson <jakob@karljakoblarsson.com>
% Lp1 2017
% 2017-10-05

Guest lecture - Ulf Norell
==========================



Fun with λ-calculus
-------------------


```
Name = String

Context : Set
Context = List (Name × Type)

data _∈_ {A : Set} (x : A) : List A → Set where
  -- atHead : ∀ {xs} → x ∈ x :: xs
  -- inTail : ∀ {y xs} → x ∈ xs → x ∈ y :: xs
  zero : ∀ {xs} → x ∈ x :: xs
  suc : ∀ {y xs} → x ∈ xs → x ∈ y :: xs

data Term (Γ : Context) : Type ⇒ Set where
  lit : (n : Nat) → Term Γ nat
  suc : Term Γ (nat => nat)
  app : ∀ {A B} (s : Term Γ (A => B)) (t : Term Γ A) → Term Γ B
  lam : ∀ {A B} (x : Name) (t : Term ((x , A) :: Γ) B) → Term Γ (A => B)


```
