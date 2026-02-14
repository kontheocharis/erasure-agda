module Models.SO.FamSet where

open import Theories.TTwE
open import Theories.LC
open import Agda.Primitive
open import Data.Unit.Polymorphic renaming (⊤ to Unit*; tt to tt*)
open import Data.Nat using (ℕ; suc)
open import Utils
open import Mode

module FamSet-TTwE {ℓ} (ϕ : Prop) where
  open TTwE 
  open TTwE-sorts 
  open TTwE-ctors

  fs-sorts : TTwE-sorts {lsuc ℓ} {ℓ}
  fs-sorts .# = ϕ
  fs-sorts .Ty = Set ℓ
  fs-sorts .Tm z A = ϕ → A
  fs-sorts .Tm ω A = A
  fs-sorts .↓ x = x
  fs-sorts .↑ p x = x p
  fs-sorts .↓↑ = refl
  fs-sorts .↑↓ {p = p} = refl

  fs-ctors : TTwE-ctors fs-sorts
  fs-ctors .Π z A B = (a : ϕ → A) → B a
  fs-ctors .Π ω A B = (a : A) → B (λ _ → a)
  fs-ctors .lam {z} f = f
  fs-ctors .lam {ω} f = f
  fs-ctors .app {z} f x = f x
  fs-ctors .app {ω} f x = f x
  fs-ctors .lam-app {z} = refl
  fs-ctors .lam-app {ω} = refl
  fs-ctors .app-lam {j = z} = refl
  fs-ctors .app-lam {j = ω} = refl
  fs-ctors .U = {!   !}
  fs-ctors .El _ = {!   !}
  fs-ctors .Nat = {!  Lift ℕ !}
  fs-ctors .zero = {!   !}
  fs-ctors .succ x = {!   !}
  fs-ctors .elim-Nat X ze su n = {!   !}
  fs-ctors .elim-Nat-zero = {!   !}
  fs-ctors .elim-Nat-succ = {!   !}

  fs : TTwE {lsuc ℓ} {ℓ}
  fs .sorts = fs-sorts
  fs .ctors = fs-ctors
