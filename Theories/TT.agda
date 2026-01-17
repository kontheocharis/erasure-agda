module Theories.TT where

open import Agda.Primitive
open import Utils
open import Mode

private
  variable
    ℓ ℓ' ℓp ℓty ℓtm : Level

record TT-sorts {ℓty} {ℓtm} : Set (lsuc (ℓty ⊔ ℓtm)) where
  field
    Ty : Set ℓty
    Tm : Ty → Set ℓtm

  coeTm : ∀ {A B} → A ≡ B → Tm A → Tm B
  coeTm p a = coe (cong Tm p) a
    
module _ (sorts : TT-sorts {ℓty} {ℓtm}) where
  open TT-sorts sorts
  
  private
    variable
      A B C : Ty
      X Y Z : Tm _ → Ty
      t u v : Tm _
      f g h : (a : Tm _) → Tm _
      eq : _ ≡ _
  
  record TT-ctors : Set (lsuc (ℓty ⊔ ℓtm)) where
    field
      -- Pi types
      Π : (A : Ty) → (Tm A → Ty) → Ty
      lam : ((a : Tm A) → Tm (X a)) → Tm (Π A X)
      app : Tm (Π A X) → (a : Tm A) → Tm (X a)

      -- Beta rules for irrelevant fragment
      lam-app : lam (app t) ≡ t
      app-lam : app (lam f) t ≡ f t

      -- Universe
      U : Ty
      El : Tm U → Ty

      -- Natural numbers
      Nat : Ty
      zero : Tm Nat
      succ : Tm Nat → Tm Nat
      elim-Nat : (X : Tm Nat → Ty)
        → (Tm (X zero))
        → ((n : Tm Nat) → Tm (X n) → Tm (X (succ n)))
        → (n : Tm Nat) → Tm (X n)

      -- Computation for elim-Nat
      elim-Nat-zero : ∀ {mz ms} → elim-Nat X mz ms zero ≡ mz
      elim-Nat-succ : ∀ {mz ms n} → elim-Nat X mz ms (succ n) ≡ ms n (elim-Nat X mz ms n)

record TT {ℓty} {ℓtm} : Set (lsuc (ℓty ⊔ ℓtm)) where
  field
    sorts : TT-sorts {ℓty} {ℓtm}
  open TT-sorts sorts public
  field
    ctors : TT-ctors sorts
  open TT-ctors ctors public
