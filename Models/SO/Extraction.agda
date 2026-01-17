module Models.SO.Extraction where

open import Theories.TTwE
open import Theories.LC
open import Agda.Primitive
open import Data.Unit.Polymorphic renaming (⊤ to Unit*; tt to tt*)
open import Utils
open import Mode

module LC-TTwE {ℓ} {ℓ'} (l : LC {ℓ'}) where
  open LC
  open TTwE 
  open TTwE-sorts 
  open TTwE-ctors

  ex-sorts : TTwE-sorts {lzero} {ℓ} {ℓ'}
  ex-sorts .# = ⊥
  ex-sorts .Ty = Unit*
  ex-sorts .Tm z tt* = Unit*
  ex-sorts .Tm ω tt* = l .Λ
  ex-sorts .↓ _ = tt*
  ex-sorts .↑ = λ ()
  ex-sorts .↓↑ = refl
  ex-sorts .↑↓ {p = p} = exfalso-prop p

  ex-ctors : TTwE-ctors ex-sorts
  ex-ctors .Π j A B = tt*
  ex-ctors .lam {z} f = f tt*
  ex-ctors .lam {ω} f = l .lambda f
  ex-ctors .app {z} f x = f
  ex-ctors .app {ω} f x = l .apply f x
  ex-ctors .lam-app {z} = refl
  ex-ctors .lam-app {ω} = l .eta _
  ex-ctors .app-lam {z} = refl
  ex-ctors .app-lam {ω} = l .beta _ _
  ex-ctors .U = tt*
  ex-ctors .El _ = tt*
  ex-ctors .Nat = tt*
  ex-ctors .zero = zeroΛ l
  ex-ctors .succ x = succΛ l x
  ex-ctors .elim-Nat X ze su n = recΛ l ze su n 
  ex-ctors .elim-Nat-zero = recΛβ-zero l
  ex-ctors .elim-Nat-succ = recΛβ-succ l

  ex : TTwE {lzero} {ℓ} {ℓ'}
  ex .sorts = ex-sorts
  ex .ctors = ex-ctors