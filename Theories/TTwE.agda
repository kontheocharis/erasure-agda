{-# OPTIONS --allow-unsolved-metas --type-in-type #-}
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
    
module _ (sorts : TTwE-sorts ) where
  open TTwE-sorts sorts
  
  private
    variable
      A B C : Ty
      A# B# C# : # → Ty
      X Y Z : Tm z A → Ty
      X# Y# Z# : (p : #) → Tm z A → Ty
      t u v v' : Tm i A
      t# u# v# : (p : #) → Tm i A
      f g h : (a : Tm j B) → Tm i A
      
  ↓* : Tm i A → Tm z A
  ↓* {i = z} t = t
  ↓* {i = ω} t = ↓ (λ _ → t)
      
  record TTwE-ctors : Set where
    field
      -- Pi types
      Π : (j : Mode) → (A : Ty) → (Tm z A → Ty) → Ty
      lam : ((a : Tm j A) → Tm ω (X (↓* a))) → Tm ω (Π j A X)
      app : Tm ω (Π j A X) → (a : Tm j A) → Tm ω (X (↓* a))
      lam-app : lam {j} (app t) ≡ t
      app-lam : ∀ {A} {X : Tm z A → Ty} {j} {f : (a : Tm j A) → Tm ω (X (↓* a))} → app {j} (lam {A = A} {X = X} f) ≡ f

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

    opaque
      unfolding coe

      ap-Tm : A ≡ B → Tm i A ≡ Tm i B
      ap-Tm refl = refl

      ap-Π : (p : A ≡ B) → X ≡[ ap-→ (ap-Tm p) refl ] Y → Π i A X ≡ Π i B Y
      ap-Π refl refl = refl

      ap-app : t ≡ u → (p : v ≡ v') → app {j = j} {X = X}  t v ≡[ cong (λ x → Tm ω (X (↓* x))) p ] app u v'
      ap-app refl refl = refl

      ap-$' : (pA : A ≡ B) → (pX : X ≡[ ap-→ (ap-Tm pA) refl ] Y) → (p : v ≡[ ap-Tm pA ] v') → X (↓* {j} v) ≡ Y (↓* {j} v')
      ap-$' refl refl refl = refl

      ap-app' : ∀ {t : Tm ω (Π ω A X)} {u : Tm ω (Π ω A X)} {v : Tm ω A} {v' : Tm z A} {π}
        → (pX : X (↓* v) ≡ X v')
        → t ≡ u
        → (p : v ≡ (↑ π v'))
        → app {A = A} {X = X} t v ≡[ ap-Tm pX ] coe (ap-Tm (cong X ↓↑)) (app {A = A} {X = X} u (↑ π v'))
      ap-app' q refl refl = refl

      swap-↓ : (∀ p → t# p ≡ ↑ p u) → ↓ t# ≡ u
      swap-↓ f = trans (cong ↓ (propfunext f)) ↓↑

    lamz-appz : lamz {X = X} {j = j} (appz t) ≡ t
    lamz-appz {j = z} {t = t} =
      trans (cong ↓ (propfunext (λ p → cong lam (funext (λ x → ↑↓)))))
      (trans (cong ↓ (propfunext (λ p → lam-app))) ↓↑)
    lamz-appz {j = ω} {t = t} =
      trans (cong ↓ (propfunext (λ p → cong lam (funext (λ x → ↑↓))))) (trans
      (cong ↓ (propfunext (λ p → trans (cong lam (funext (λ x → ap-app refl
      ↑↓))) lam-app))) ↓↑)

    appz-lamz : ∀ {j} {X : Tm z A → Ty} {f : (a : Tm z A) → Tm z (X a)} → appz {j = j} {X = X} (lamz {j = j} f) ≡ f
    appz-lamz {j = z} {f = f} = funext (λ t → 
      trans (cong ↓ (propfunext (λ p → cong (λ g → app g t) ↑↓)))
            (trans (cong ↓ (propfunext (λ p → (ap-$ app-lam t)))) ↓↑))
    appz-lamz {j = ω} {X = X} {f = f} = funext (λ t →
      trans (cong ↓ (propfunext (λ p → ap-app' {u = lam λ a → ↑ p (f (↓* a))}
        (cong X ↓↑) ↑↓ refl))) (swap-↓ (λ p → transᴰ (dep
        (ap-$ app-lam (↑ p t))) (congᴰ (λ t → Tm ω (X t)) (λ t → ↑ p (f t)) ↓↑))))
  
    zeroz : Tm z Nat
    zeroz = ↓* zero

    succz : Tm z Nat → Tm z Nat
    succz n = ↓ (λ p → succ (↑ p n))

    elim-Natz : (X : Tm z Nat → Ty)
      → (Tm z (X zeroz))
      → ((n : Tm z Nat) → Tm z (X n) → Tm z (X (succz n)))
      → (n : Tm z Nat) → Tm z (X n)
    elim-Natz X ze su n = coe (ap-Tm (cong X ↓↑)) (↓ λ p →
      elim-Nat X (↑ p ze) (λ n pn → coe (ap-Tm (cong X (cong ↓ (propfunext  λ p → cong succ ↑↓))))
      (↑ p (su (↓* n) (↓* pn)))) (↑ p n))

    -- Can also derive the eliminator rules..


record TTwE {ℓp} {ℓty} {ℓtm} : Set (lsuc (ℓp ⊔ ℓty ⊔ ℓtm)) where
  field
    sorts : TTwE-sorts {ℓp} {ℓty} {ℓtm}
  open TTwE-sorts sorts public
  field
    ctors : TTwE-ctors sorts
  open TTwE-ctors ctors public
