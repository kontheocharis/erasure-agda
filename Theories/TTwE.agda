{-# OPTIONS --allow-unsolved-metas #-}
module Theories.TTwE where

open import Agda.Primitive
open import Utils
open import Mode

private
  variable
    ℓ ℓ' ℓp ℓty ℓtm : Level

record TTwE-sorts {ℓp} {ℓty} {ℓtm} : Set (lsuc (ℓp ⊔ ℓty ⊔ ℓtm)) where
  field
    # : Prop ℓp
    Ty : Set ℓty
    Tm : Mode → Ty → Set ℓtm

    ↓ : ∀ {A} → (# → Tm ω A) → Tm z A
    ↑ : ∀ {A} → # → Tm z A → Tm ω A
    ↓↑ : ∀ {A} {t : Tm z A} → ↓ (λ p → ↑ p t) ≡ t
    ↑↓ : ∀ {A} {t# : # → Tm ω A} {p : #} → ↑ p (↓ t#) ≡ t# p

  coeTm : ∀ {A B} → A ≡ B → Tm i A → Tm i B
  coeTm {i = i} p a = coe (cong (Tm i) p) a
    
module _ (sorts : TTwE-sorts {ℓp} {ℓty} {ℓtm}) where
  open TTwE-sorts sorts
  
  private
    variable
      A B C : Ty
      A# B# C# : # → Ty
      X Y Z : Tm _ _ → Ty
      X# Y# Z# : (p : #) → Tm _ _ → Ty
      t u v : Tm _ _
      t# u# v# : (p : #) → Tm _ _
      f g h : (a : Tm _ _) → Tm _ _
      eq : _ ≡ _
      
  ↓* : Tm i A → Tm z A
  ↓* {i = z} t = t
  ↓* {i = ω} t = ↓ (λ _ → t)
      
  record TTwE-ctors : Set (lsuc (ℓp ⊔ ℓty ⊔ ℓtm)) where
    field
      -- Pi types
      Π : (j : Mode) → (A : Ty) → (Tm z A → Ty) → Ty
      lam : ((a : Tm j A) → Tm ω (X (↓* a))) → Tm ω (Π j A X)
      app : Tm ω (Π j A X) → (a : Tm j A) → Tm ω (X (↓* a))

      -- Beta rules for irrelevant fragment
      lam-app : lam {j} (app t) ≡ t
      app-lam : app {j} (lam f) t ≡ f t

      -- Universe
      U : Ty
      El : Tm z U → Ty

      -- Natural numbers
      Nat : Ty
      zero : Tm ω Nat
      succ : Tm ω Nat → Tm ω Nat
      elim-Nat : (X : Tm z Nat → Ty)
        → (Tm ω (X (↓* zero)))
        → ((n : Tm ω Nat) → Tm ω (X (↓* n)) → Tm ω (X (↓* (succ n))))
        → (n : Tm ω Nat) → Tm ω (X (↓* n))

      -- Computation for elim-Nat
      elim-Nat-zero : ∀ {mz ms} → elim-Nat X mz ms zero ≡ mz
      elim-Nat-succ : ∀ {mz ms n} → elim-Nat X mz ms (succ n) ≡ ms n (elim-Nat X mz ms n)

    lamz : ((a : Tm z A) → Tm z (X a)) → Tm z (Π j A X)
    lamz f = ↓ (λ p → lam (λ x → ↑ p (f (↓* x))) ) 

    appz : Tm z (Π j A X) → (a : Tm z A) → Tm z (X a)
    appz {j = z} f x = ↓ (λ p → app (↑ p f) x)
    appz {j = ω} {X = X} f x = ↓ (λ p → coeTm (cong X ↓↑) (app (↑ p f) (↑ p x) ))

    -- lamz-appz : lamz {j} (appz t) ≡ t
    -- lamz-appz {t = t} =
    --   ({!   !})

    -- appz-lamz : appz {j} (lamz f) t ≡ f t
    -- appz-lamz {f = f} {t = t} =
    --   ({!   !})

    lamz-appz : lamz {X = X} {j = j} (appz t) ≡ t
    lamz-appz = {!   !}
    -- lamz-appz {X = X} {j = ω} {t = t} = {!   !}

    appz-lamz : appz {j = j} {X = X} (lamz f) t ≡ f t
    appz-lamz = {!   !}
    -- appz-lamz {j = ω} {X = X} {f = f} {t = t} = {!   !}

    zeroz : Tm z Nat
    zeroz = ↓* zero

    succz : Tm z Nat → Tm z Nat
    succz n = ↓ (λ p → succ (↑ p n))

    elim-Natz : (X : Tm z Nat → Ty)
      → (Tm z (X zeroz))
      → ((n : Tm z Nat) → Tm z (X n) → Tm z (X (succz n)))
      → (n : Tm z Nat) → Tm z (X n)
    elim-Natz X ze su n = {!   !} -- coeTm (cong X ↓↑)
      -- [ (λ p → elim-Nat X (↑[ p ] ze) (λ k pk → coeTm ({!   !})
      --   (↑[ p ] (su [ k ]* [ pk ]*))) (↑[ p ] n)) ]

    -- Computation for elim-Nat
    elim-Nat-zeroz : ∀ {mz ms} → elim-Natz X mz ms zeroz ≡ mz
    elim-Nat-zeroz = {! !}

    elim-Nat-succz : ∀ {mz ms n} → elim-Natz X mz ms (succz n) ≡ ms n (elim-Natz X mz ms n)
    elim-Nat-succz = {! !}


record TTwE {ℓp} {ℓty} {ℓtm} : Set (lsuc (ℓp ⊔ ℓty ⊔ ℓtm)) where
  field
    sorts : TTwE-sorts {ℓp} {ℓty} {ℓtm}
  open TTwE-sorts sorts public
  field
    ctors : TTwE-ctors sorts
  open TTwE-ctors ctors public