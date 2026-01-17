module Models.SO.Conservativity where

open import Theories.TTwE
open import Theories.TT
open import Agda.Primitive
open import Utils
open import Mode

-- TT model of TTwE
module TT-TTwE {ℓ} {ℓ'} (m : TT {ℓ} {ℓ'}) where
  open TT
  open TTwE 
  open TTwE-sorts 
  open TTwE-ctors

  f-sorts : TTwE-sorts {lzero} {ℓ} {ℓ'}
  f-sorts .# = ⊤
  f-sorts .Ty = m .Ty
  f-sorts .Tm j A = m .Tm A
  f-sorts .↓ x = x tt
  f-sorts .↑ x x₁ = x₁
  f-sorts .↑↓ = refl
  f-sorts .↓↑ = refl

  f-ctors : TTwE-ctors f-sorts
  f-ctors .Π j A B = m .Π A B
  f-ctors .lam {z} f = m .lam f
  f-ctors .lam {ω} f = m .lam f
  f-ctors .app {z} = m .app 
  f-ctors .app {ω} = m .app
  f-ctors .lam-app {z} = m .lam-app
  f-ctors .lam-app {ω} = m .lam-app
  f-ctors .app-lam {z} = m .app-lam
  f-ctors .app-lam {ω} = m .app-lam
  f-ctors .U = m .U
  f-ctors .El = m .El
  f-ctors .Nat = m .Nat
  f-ctors .zero = m .zero
  f-ctors .succ = m .succ
  f-ctors .elim-Nat = m .elim-Nat
  f-ctors .elim-Nat-zero = m .elim-Nat-zero
  f-ctors .elim-Nat-succ = m .elim-Nat-succ

  f : TTwE {lzero} {ℓ} {ℓ'}
  f .sorts = f-sorts
  f .ctors = f-ctors

-- TTwE model of TT using erased terms
module TTwE-TT {ℓ} {ℓ'} (i : TTwE {lzero} {ℓ} {ℓ'}) where
  open TTwE
  open TT 
  open TT-sorts 
  open TT-ctors

  m-sorts : TT-sorts {ℓ} {ℓ'}
  m-sorts .Ty = i .Ty
  m-sorts .Tm A = i .Tm z A

  m-ctors : TT-ctors m-sorts
  m-ctors .Π = i .Π z -- z or ω doesn't matter here
  m-ctors .lam x = TTwE.lamz i x
  m-ctors .app x y = TTwE.appz i x y
  m-ctors .lam-app = TTwE.lamz-appz i {j = z}
  m-ctors .app-lam = TTwE.appz-lamz i {j = z}
  m-ctors .U = i .U
  m-ctors .El = i .El
  m-ctors .Nat = i .Nat
  m-ctors .zero = TTwE.zeroz i
  m-ctors .succ = TTwE.succz i
  m-ctors .elim-Nat = TTwE.elim-Natz i
  m-ctors .elim-Nat-zero {ms = ms} = TTwE.elim-Nat-zeroz i {ms = ms}
  m-ctors .elim-Nat-succ {ms = ms} = TTwE.elim-Nat-succz i {ms = ms}

  m : TT {ℓ} {ℓ'}
  m .sorts = m-sorts
  m .ctors = m-ctors