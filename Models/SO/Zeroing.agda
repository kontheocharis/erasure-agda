module Models.SO.Zeroing where

open import Theories.TTwE
open import Agda.Primitive
open import Utils
open import Mode

-- Zeroing model of TTwE
module TTwE-zeroing {ℓ} {ℓ'} (m : TTwE {ℓ} {ℓ'}) where
  open TTwE 
  open TTwE-sorts 
  open TTwE-ctors

  ze-sorts : TTwE-sorts {ℓ} {ℓ'}
  ze-sorts .# = ⊤
  ze-sorts .Ty = m .Ty
  ze-sorts .Tm j A = m .Tm z A
  ze-sorts .↓ x = x tt
  ze-sorts .↑ x x₁ = x₁
  ze-sorts .↑↓ = refl
  ze-sorts .↓↑ = refl

  ze-ctors : TTwE-ctors ze-sorts
  ze-ctors .Π j A B = TTwE.Π' m j A B
  ze-ctors .lam {z} f = TTwE.lamz m {j = z} f
  ze-ctors .lam {ω} f = TTwE.lamz m {j = ω} f
  ze-ctors .app {z} = TTwE.appz m {j = z}
  ze-ctors .app {ω} = TTwE.appz m {j = ω}
  ze-ctors .lam-app {z} = TTwE.lamz-appz m
  ze-ctors .lam-app {ω} = TTwE.lamz-appz  m
  ze-ctors .app-lam {j = z} = TTwE.appz-lamz m {j = z}
  ze-ctors .app-lam {j = ω} {f = f} = TTwE.appz-lamz m {j = ω} {f = f}
  ze-ctors .U = m .U
  ze-ctors .El = m .El
  ze-ctors .Nat = m .Nat
  ze-ctors .zero = TTwE.zeroz m
  ze-ctors .succ = TTwE.succz m
  ze-ctors .elim-Nat = TTwE.elim-Natz m
  ze-ctors .elim-Nat-zero = {!   !}
  ze-ctors .elim-Nat-succ = {!   !}

  ze : TTwE {ℓ} {ℓ'}
  ze .sorts = ze-sorts
  ze .ctors = ze-ctors
