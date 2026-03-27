module Theories.TTwE where

open import Agda.Primitive
open import Utils
open import Mode

private
  variable
    ℓ ℓ' ℓp ℓty ℓtm : Level

record TTwE-sorts {ℓty} {ℓtm} : Set (lsuc (ℓty ⊔ ℓtm)) where
  field
    # : Prop
    Ty : Set ℓty
    Tm : Mode → Ty → Set ℓtm

    ↓ : ∀ {A} → (# → Tm ω A) → Tm z A
    ↑ : ∀ {A} → # → Tm z A → Tm ω A
    ↓↑ : ∀ {A} {t : Tm z A} → ↓ (λ p → ↑ p t) ≡ t
    ↑↓ : ∀ {A} {t# : # → Tm ω A} {p : #} → ↑ p (↓ t#) ≡ t# p

  coeTm : ∀ {A B} → A ≡ B → Tm i A → Tm i B
  coeTm {i = i} p a = coe (cong (Tm i) p) a
    
module _ {ℓty} {ℓtm} (sorts : TTwE-sorts {ℓty} {ℓtm}) where
  open TTwE-sorts sorts
  
  private
    variable
      A B C : Ty
      A# B# C# : # → Ty
      X Y Z : Tm j A → Ty
      X# Y# Z# : (p : #) → Tm z A → Ty
      t u v v' : Tm i A
      t# u# v# : (p : #) → Tm i A
      f g h : (a : Tm j A) → Tm ω (X a)
      
  ↓* : Tm i A → Tm z A
  ↓* {i = z} t = t
  ↓* {i = ω} t = ↓ (λ _ → t)
      
  record TTwE-ctors : Set (lsuc (ℓty ⊔ ℓtm)) where
    field
      -- Pi types
      Π : (j : Mode) → (A : Ty) → (Tm j A → Ty) → Ty
      lam : ((a : Tm j A) → Tm ω (X a)) → Tm ω (Π j A X)
      app : Tm ω (Π j A X) → (a : Tm j A) → Tm ω (X a)
      lam-app : lam {j} (app t) ≡ t
      app-lam : app {j} (lam f) ≡ f

      -- Universe
      U : Ty
      El : Tm z U → Ty
      code : Ty → Tm z U
      El-code : El (code A) ≡ A
      code-El : code (El t) ≡ t

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

    ↑T : (# → Ty) → Ty
    ↑T A = El (↓ λ p → ↑ p (code (A p)))

    Π' : (j : Mode) → (A : Ty) → (Tm z A → Ty) → Ty
    Π' j A B = Π j A (λ x → B (↓* x))

    lam' : ∀ {j} {A} {X : Tm z A → Ty} → ((a : Tm j A) → Tm ω (X (↓* a))) → Tm ω (Π' j A X)
    lam' f = lam (λ x → f x)

    app' : ∀ {j} {A} {X : Tm z A → Ty} → Tm ω (Π' j A X) → (a : Tm j A) → Tm ω (X (↓* a))
    app' x a = app x a

    lam'-app' : ∀ {j A X t} → lam' {j} {A} {X} (app' {j} {A} {X} t) ≡ t
    lam'-app' = lam-app

    app'-lam' : ∀ {j A X t} → lam' {j} {A} {X} (app' {j} {A} {X} t) ≡ t
    app'-lam' = lam-app

    lamz : ((a : Tm z A) → Tm z (X a)) → Tm z (Π' j A X)
    lamz f = ↓ (λ p → lam (λ x → ↑ p (f (↓* x))) ) 

    appz : Tm z (Π' j A X) → (a : Tm z A) → Tm z (X a)
    appz {j = z} f x = ↓ (λ p → app (↑ p f) x)
    appz {j = ω} {X = X} f x = ↓ (λ p → coeTm (cong X ↓↑) (app (↑ p f) (↑ p x) ))

    opaque
      unfolding coe

      ap-Tm : A ≡ B → Tm i A ≡ Tm i B
      ap-Tm refl = refl

      ap-Π : (p : A ≡ B) → X ≡[ ap-→ (ap-Tm p) refl ] Y → Π i A X ≡ Π i B Y
      ap-Π refl refl = refl

      ap-app : t ≡ u → (p : v ≡ v') → app {j = j} {X = X}  t v ≡[ cong (λ x → Tm ω (X x)) p ] app u v'
      ap-app refl refl = refl

      ap-$' : (pA : A ≡ B) → (pX : X ≡[ ap-→ (ap-Tm pA) refl ] Y) → (p : v ≡[ ap-Tm pA ] v') → X (↓* {j} v) ≡ Y (↓* {j} v')
      ap-$' refl refl refl = refl

      ap-app' : ∀ {t : Tm ω (Π j A X)} {u : Tm ω (Π j A X)} {v : Tm j A} {v' : Tm j A}
        → (pX : X v ≡ X v')
        → t ≡ u
        → (p : v ≡ v')
        → app {A = A} {X = X} t v ≡[ ap-Tm pX ] (app {A = A} {X = X} u v')
      ap-app' q refl refl = refl

      swap-↓ : (∀ p → t# p ≡ ↑ p u) → ↓ t# ≡ u
      swap-↓ f = trans (cong ↓ (propfunext f)) ↓↑

      ap-↑ : ∀ {A B : Ty} {a : Tm z A} {b : Tm z B} (p : #)
        → (pA : A ≡ B) → a ≡[ ap-Tm pA ] b
        → ↑ p a ≡[ ap-Tm pA ] ↑ p b
      ap-↑ p refl refl = refl

      ap-dep : ∀ {a b : Tm z A} (f : (x : Tm z A) → Tm i (X x))
        → (p : a ≡ b) → f a ≡[ ap-Tm (cong X p) ] f b
      ap-dep f refl = refl

      ap-↑∘f : ∀ {C : Ty} {X : Tm z C → Ty} {a b : Tm z C}
        → (p# : #) (f : (x : Tm z C) → Tm z (X x))
        → (eq : a ≡ b)
        → coeTm (cong X eq) (↑ p# (f a)) ≡ ↑ p# (f b)
      ap-↑∘f p# f refl = refl

    lamz-appz : lamz {X = X} {j = j} (appz t) ≡ t
    lamz-appz {j = z} {t = t} =
      trans (cong ↓ (propfunext (λ p → cong lam (funext (λ x → ↑↓)))))
      (trans (cong ↓ (propfunext (λ p → lam-app))) ↓↑)
    lamz-appz {j = ω} {t = t} =
      trans (cong ↓ (propfunext (λ p → cong lam (funext (λ x → ↑↓))))) (trans
      (cong ↓ (propfunext (λ p → trans (cong lam (funext (λ x → ap-app refl
      ↑↓))) lam-app))) ↓↑)

    appz-lamz : ∀ {j} {X : Tm z A → Ty} {f : (a : Tm z A) → Tm z (X a)} → appz {j = j} {X = X} (lamz {j = j} f) ≡ f
    appz-lamz {j = z} {f = f} = funext (λ a →
      swap-↓ (λ p → trans (cong (λ g → app g a) ↑↓) (ap-$ app-lam a)))
    appz-lamz {j = ω} {X = X} {f = f} = funext (λ a →
      swap-↓ (λ p →
        let ↓*↑ : ↓* (↑ p a) ≡ a
            ↓*↑ = trans (cong ↓ (propfunext λ _ → refl)) (↓↑ {t = a})
            step1 = cong (λ g → app g (↑ p a)) ↑↓
            step2 = ap-$ (app-lam {f = λ x → ↑ p (f (↓* x))}) (↑ p a)
            step3 : coeTm (cong X ↓*↑) (↑ p (f (↓* (↑ p a)))) ≡ ↑ p (f a)
            step3 = ap-↑∘f p f ↓*↑
        in trans (cong (coeTm (cong X ↓*↑)) (trans step1 step2)) step3))

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

    -- @TODO: Can also derive the eliminator rules..

record TTwE {ℓty} {ℓtm} : Set (lsuc (ℓty ⊔ ℓtm)) where
  field
    sorts : TTwE-sorts {ℓty} {ℓtm}
  open TTwE-sorts sorts public
  field
    ctors : TTwE-ctors sorts
  open TTwE-ctors ctors public
