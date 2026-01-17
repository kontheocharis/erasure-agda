{-# OPTIONS --type-in-type #-}
module Models.FO.ExtractionCorrectness where

open import Data.Product
open import Data.Product.Properties
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding (zero)
open import Data.Vec

open import Utils hiding (⊤; ⊥)
open import Theories.CwFwE
open import Mode

postulate
  Λ : Set
  ƛ : (Λ → Λ) → Λ
  _＠_ : Λ → Λ → Λ
  Λη : ∀ f →  ƛ (f ＠_) ≡ f
  Λβ : ∀ f x → (ƛ f) ＠ x ≡ f x
  {-# REWRITE Λη Λβ #-}

  zeroΛ : Λ
  succΛ : Λ → Λ
  recΛ : Λ → (Λ → Λ → Λ) → Λ → Λ
  recΛβ-zero : ∀ {zr su} → recΛ zr su zeroΛ ≡ zr
  recΛβ-succ : ∀ {zr su n} → recΛ zr su (succΛ n) ≡ su n (recΛ zr su n)
  {-# REWRITE recΛβ-zero recΛβ-succ #-}

  zeroΛ≠succΛ : ∀ {x} → zeroΛ ≡ succΛ x → ⊥
{-# INJECTIVE succΛ #-}

succΛ-inj : ∀ {x y} → succΛ x ≡ succΛ y → x ≡ y
succΛ-inj refl = refl

embed-nat : ℕ → Λ
embed-nat ℕ.zero = zeroΛ
embed-nat (suc x) = succΛ (embed-nat x)

embed-nat-inj : ∀ n m → embed-nat n ≡ embed-nat m → n ≡ m
embed-nat-inj ℕ.zero ℕ.zero p = refl
embed-nat-inj ℕ.zero (suc m) p = ⊥-elim-prop (zeroΛ≠succΛ p)
embed-nat-inj (suc n) ℕ.zero p = ⊥-elim-prop (zeroΛ≠succΛ (sym p))
embed-nat-inj (suc n) (suc m) p = cong suc (embed-nat-inj _ _ (succΛ-inj p))

module _ where
  open CwFwE-sorts
  open in-CwFwE-sorts
  open CwFwE-core
  open in-CwFwE-core

  fam-s : CwFwE-sorts
  fam-s .Con =
    Σ[ Γₛ ∈ Set ]
    Σ[ Γₑ ∈ Set ]
    Σ[ Γ₀ ∈ (Γₛ → Set) ]
    ((γₛ : Γₛ) → Γₑ → Γ₀ γₛ → Set)
  fam-s .Sub (Γₛ , Γₑ , Γ₀ , Γ₁) (Δₛ , Δₑ , Δ₀ , Δ₁) =
    Σ[ σₛ ∈ (Γₛ → Δₛ) ]
    Σ[ σₑ ∈ (Γₑ → Δₑ) ]
    Σ[ σ₀ ∈ (∀ γₛ → Γ₀ γₛ → Δ₀ (σₛ γₛ)) ]
    (∀ γₛ γₑ γ → Γ₁ γₛ γₑ γ → Δ₁ (σₛ γₛ) (σₑ γₑ) (σ₀ γₛ γ))  
  fam-s .Ty (Γₛ , Γₑ , Γ₀ , Γ₁) =
    Σ[ Aₛ ∈ (Γₛ → Set) ]
    Σ[ A₀ ∈ (∀ γₛ → Γ₀ γₛ → Aₛ γₛ → Set) ]
    (∀ γₛ γ → (aₛ : Aₛ γₛ) → Λ → A₀ γₛ γ aₛ → Set)
  fam-s .Tm (Γₛ , Γₑ , Γ₀ , Γ₁) ω (Aₛ , A₀ , A₁) =
    Σ[ aₛ ∈ ((γ : Γₛ) → Aₛ γ) ]
    Σ[ aₑ ∈ (Γₑ → Λ) ] 
    Σ[ a₀ ∈ (∀ γₛ → (γ : Γ₀ γₛ) → A₀ γₛ γ (aₛ γₛ)) ]
    (∀ γₛ γₑ γ → (γ' : Γ₁ γₛ γₑ γ) → A₁ γₛ γ (aₛ γₛ) (aₑ γₑ) (a₀ γₛ γ)) 
  fam-s .Tm (Γₛ , Γₑ , Γ₀ , Γ₁) z (Aₛ , A₀ , A₁) =
    Σ[ aₛ ∈ ((γₛ : Γₛ) → Aₛ γₛ) ]
    (∀ γₛ → (γ : Γ₀ γₛ) → A₀ γₛ γ (aₛ γₛ))
  fam-s .#∈ (Γₛ , Γₑ , Γ₀ , Γ₁) = Γₑ → ⊥

  fam-c : CwFwE-core fam-s
  fam-c .id = (λ z₁ → z₁) , (λ z₁ → z₁) , (λ γₛ z₁ → z₁) , (λ γₛ γₑ γ z₁ → z₁)
  (fam-c ∘ (σₛ , σₑ , σ₀ , σ₁)) (τₛ , τₑ , τ₀ , τ₁) =
    (λ z₁ → σₛ (τₛ z₁)) ,
     (λ z₁ → σₑ (τₑ z₁)) ,
     (λ γₛ z₁ → σ₀ (τₛ γₛ) (τ₀ γₛ z₁)) ,
     (λ γₛ γₑ γ z₁ → σ₁ (τₛ γₛ) (τₑ γₑ) (τ₀ γₛ γ) (τ₁ γₛ γₑ γ z₁))
  fam-c .assoc = refl
  fam-c .∘id = refl
  fam-c .id∘ = refl
  fam-c .∙ = ⊤ , ⊤ , (λ _ → ⊤) , (λ _ _ _ → ⊤)
  fam-c .ε = (λ _ → tt) , (λ _ → tt) , (λ γₛ _ → tt) , (λ γₛ γₑ γ _ → tt)
  fam-c .∃!ε = refl
  (fam-c [ Aₛ , A₀ , A₁ ]T) (σₛ , σₑ , σ₀ , σ₁) =
    (λ γₛ → Aₛ (σₛ γₛ))
    , (λ γₛ γ → A₀ (σₛ γₛ) (σ₀ γₛ γ))
    , (λ γₛ γ aₛ a → A₁ (σₛ γₛ) (σ₀ γₛ γ) aₛ a)
  fam-c ._[_] {i = ω} (tₛ , tₑ , t₀ , t₁) (σₛ , σₑ , σ₀ , σ₁) =
    (λ γ → tₛ (σₛ γ)) ,
      (λ z₁ → tₑ (σₑ z₁)) ,
      (λ γₛ γ → t₀ (σₛ γₛ) (σ₀ γₛ γ)) ,
      (λ γₛ γₑ γ γ' → t₁ (σₛ γₛ) (σₑ γₑ) (σ₀ γₛ γ) (σ₁ γₛ γₑ γ γ'))
  fam-c ._[_] {i = z} (tₛ , t₀) (σₛ , σₑ , σ₀ , σ₁) =
    (λ γₛ → tₛ (σₛ γₛ)) , (λ γₛ γ → t₀ (σₛ γₛ) (σ₀ γₛ γ))
  fam-c .[id]T = refl
  fam-c .[id] {i = z} = refl
  fam-c .[id] {i = ω} = refl
  fam-c .[∘]T = refl
  fam-c .[∘] {i = z} = refl
  fam-c .[∘] {i = ω} = refl
  (fam-c ▷[ (Γₛ , Γₑ , Γ₀ , Γ₁) ] ω) (Aₛ , A₀ , A₁) =
    (Σ[ γₛ ∈ Γₛ ] Aₛ γₛ)
    , (Γₑ × Λ)
    , (λ (γₛ , aₛ) → Σ[ γ ∈ Γ₀ γₛ ] A₀ γₛ γ aₛ)
    , λ (γₛ , aₛ) (γₑ , aₑ) (γ , a) → Σ[ γ' ∈ Γ₁ γₛ γₑ γ ] A₁ γₛ γ aₛ aₑ a
  (fam-c ▷[ (Γₛ , Γₑ , Γ₀ , Γ₁) ] z) (Aₛ , A₀ , A₁) =
    (Σ[ γₛ ∈ Γₛ ] Aₛ γₛ)
    , Γₑ
    , (λ (γₛ , aₛ) → Σ[ γ ∈ Γ₀ γₛ ] A₀ γₛ γ aₛ)
    , λ (γₛ , aₛ) γₑ (γ , a) → Γ₁ γₛ γₑ γ
  fam-c .p {i = ω} =
    (λ z₁ → z₁ .proj₁) ,
     (λ z₁ → z₁ .proj₁) ,
     (λ γₛ z₁ → z₁ .proj₁) , (λ γₛ γₑ γ z₁ → z₁ .proj₁)
  fam-c .p {i = z} =
    (λ z₁ → z₁ .proj₁) ,
     (λ z₁ → z₁) , (λ γₛ z₁ → z₁ .proj₁) , (λ γₛ γₑ γ z₁ → z₁)
  fam-c .q {i = ω} =
    (λ γ → γ .proj₂) ,
     (λ z₁ → z₁ .proj₂) ,
     (λ γₛ γ → γ .proj₂) , (λ γₛ γₑ γ γ' → γ' .proj₂)
  fam-c .q {i = z} =
    (λ γₛ → γₛ .proj₂) , (λ γₛ γ → γ .proj₂)
  fam-c ._,,_ {i = ω} (σₛ , σₑ , σ₀ , σ₁) (tₛ , tₑ , t₀ , t₁)
    = (λ z₁ → σₛ z₁ , tₛ z₁) ,
       (λ z₁ → σₑ z₁ , tₑ z₁) ,
       (λ γₛ z₁ → σ₀ γₛ z₁ , t₀ γₛ z₁) ,
       (λ γₛ γₑ γ z₁ → σ₁ γₛ γₑ γ z₁ , t₁ γₛ γₑ γ z₁)
  fam-c ._,,_ {i = z} (σₛ , σₑ , σ₀ , σ₁) (tₛ , t₀)
    = (λ z₁ → σₛ z₁ , tₛ z₁) , σₑ , (λ γₛ z₁ → σ₀ γₛ z₁ , t₀ γₛ z₁) , σ₁
  fam-c .,∘ {i = z} = refl
  fam-c .,∘ {i = ω} = refl
  fam-c .p,q {i = z} = refl
  fam-c .p,q {i = ω} = refl
  fam-c .p∘, {i = z} = refl
  fam-c .p∘, {i = ω} = refl
  fam-c .q[,] {i = z} = refl
  fam-c .q[,] {i = ω} = refl

  (fam-c [ t ]#) σ γ = t (σ .proj₂ .proj₁ γ)
  fam-c .[id]# = refl
  fam-c .[∘]# = refl
  (fam-c ▷#) (Γₛ , Γₑ , Γ₀ , Γ₁) = Γₛ , ⊥ , Γ₀ , λ _ _ _ → ⊥
  fam-c .p# = (λ z₁ → z₁) , (λ ()) , (λ γₛ z₁ → z₁) , λ γ ()
  fam-c .q# γ = γ
  (fam-c ,# σ) π = σ .proj₁ , π , σ .proj₂ .proj₂ .proj₁ , (λ γₛ γₑ γ z₁ → π γₑ)
  fam-c .,#∘ = refl
  fam-c .p,#q = refl
  fam-c .p∘,# {π = π} =
    Σ≡ refl (Σ≡ (funext (λ γₑ → ⊥-elim-prop (π γₑ)))
      (Σ≡ refl ( funext (λ γₛ → funext (λ γₑ → ⊥-elim-prop (π γₑ))))))
  fam-c .q[,#] = refl
  fam-c .↓ (xₛ , xₑ , x₀ , x₁) = xₛ , x₀
  fam-c .↓[] = refl
  fam-c .↑ (xₛ , x₀) = xₛ , (λ ()) , x₀ , λ γₛ ()
  fam-c .↑↓ {t = t} = Σ≡ refl (Σ≡ (funext (λ ()))
    (Σ≡ refl (funext (λ x → funext (λ y → ⊥-elim-prop y)))))
  fam-c .↓↑ = refl
  fam-c .pz∘⁺≡⁺∘pz' = refl

  open Π-structure

  fam-Π : Π-structure fam-s fam-c
  fam-Π .Π ω (Aₛ , A₀ , A₁) (Bₛ , B₀ , B₁) =
    (λ γ → (a : Aₛ γ) → Bₛ (γ , a))
    , (λ γₛ γ fₛ → ∀ aₛ → (a : A₀ γₛ γ aₛ) → B₀ (γₛ , aₛ) (γ , a) (fₛ aₛ))
    , λ γₛ γ fₛ fₑ f₀
      → ∀ aₛ aₑ a → A₁ γₛ γ aₛ aₑ a → B₁ (γₛ , aₛ) (γ , a) (fₛ aₛ) (fₑ ＠ aₑ) (f₀ aₛ a)
  fam-Π .Π z (Aₛ , A₀ , A₁) (Bₛ , B₀ , B₁) =
    (λ γ → (a : Aₛ γ) → Bₛ (γ , a))
    , (λ γₛ γ fₛ → ∀ aₛ → (a : A₀ γₛ γ aₛ) → B₀ (γₛ , aₛ) (γ , a) (fₛ aₛ))
    , λ γₛ γ fₛ fₑ f₀
      → ∀ aₛ a → B₁ (γₛ , aₛ) (γ , a) (fₛ aₛ) fₑ (f₀ aₛ a)
  fam-Π .Π[] {i = ω} = refl
  fam-Π .Π[] {i = z} = refl
  fam-Π .lam {i = ω} (fₛ , fₑ , f₀ , f₁) =
     (λ γ a → fₛ (γ , a))
    , (λ γₑ → ƛ (λ x → fₑ (γₑ , x)))
     , (λ γₛ γ aₛ a → f₀ (γₛ , aₛ) (γ , a))
     , λ γₛ γₑ γ γ' aₛ aₑ a a' → f₁ (γₛ , aₛ) (γₑ , aₑ) (γ , a) (γ' , a')
  fam-Π .lam {i = z} (fₛ , fₑ , f₀ , f₁) =
     (λ γ a → fₛ (γ , a))
     , fₑ
     , (λ γₛ γ aₛ a → f₀ (γₛ , aₛ) (γ , a))
     , λ γₛ γₑ γ γ' aₛ a → f₁ (γₛ , aₛ) γₑ (γ , a) γ' 
  fam-Π .lam[] {i = z} = refl
  fam-Π .lam[] {i = ω} = refl
  fam-Π .ap {i = z} (tₛ , tₑ , t₀ , t₁) =
    (λ (γ , a) → tₛ γ a)
    , tₑ
    , (λ (γₛ , aₛ) (γ , a) → t₀ γₛ γ aₛ a)
    , λ (γₛ , aₛ) γₑ (γ , a) γ' → t₁ γₛ γₑ γ γ' aₛ a
  fam-Π .ap {i = ω} (tₛ , tₑ , t₀ , t₁) =
    (λ (γ , a) → tₛ γ a)
    , (λ (γₑ , aₑ) → tₑ γₑ ＠ aₑ)
    , (λ (γₛ , aₛ) (γ , a) → t₀ γₛ γ aₛ a)
    , λ (γₛ , aₛ) (γₑ , aₑ) (γ , a) (γ' , a') → t₁ γₛ γₑ γ γ' aₛ aₑ a a'
  fam-Π .Πβ {i = z} = refl
  fam-Π .Πβ {i = ω} = refl
  fam-Π .Πη {i = z} = refl
  fam-Π .Πη {i = ω} = refl

  open U-structure

  fam-U : U-structure fam-s fam-c
  fam-U .U =
    (λ γ → Set)
    , (λ γₛ γ Aₛ → Σ[ A₀ ∈ (Aₛ → Set) ] ((aₛ : Aₛ) → Λ → A₀ aₛ → Set))
    , λ γ γₛ aₛ aₑ a₀ → ⊤
  fam-U .U[] = refl
  fam-U .El (tₛ , t₀) =
     tₛ , (λ γₛ γ aₛ → t₀ γₛ γ .proj₁ aₛ) , λ γₛ γ aₛ aₑ aₒ → t₀ γₛ γ .proj₂ aₛ aₑ aₒ
  fam-U .El[] = refl
  fam-U .code (Aₛ , A₀ , A₁) = Aₛ , λ γₛ γ → A₀ γₛ γ , A₁ γₛ γ
  fam-U .code[] = refl
  fam-U .El-code = refl
  fam-U .code-El = refl

open CwFwE-sorts fam-s
open in-CwFwE-sorts fam-s
open CwFwE-core fam-c
open in-CwFwE-core fam-c
open Π-structure fam-Π
open U-structure fam-U

Nat : Ty Γ
Nat =
  (λ γ → ℕ) 
  , (λ γₛ z₁ z₂ → ⊤)
  , λ γₛ γ aₛ aₑ a₀ → (aₑ ≡ embed-nat aₛ) true

zero : Tm Γ ω (Nat {Γ})
zero =
  (λ γ → 0)
  , (λ _ → zeroΛ)
  , (λ γₛ γ → tt)
  , (λ γₛ γₑ γ γ' → by refl)

succ : Tm Γ ω (Nat {Γ}) → Tm Γ ω (Nat {Γ})
succ (nₛ , nₑ , n₀ , n₁) =
  (λ γ → suc (nₛ γ))
  , (λ γₑ → succΛ (nₑ γₑ) )
  , (λ γₛ γ → tt)
  , λ γₛ γₑ γ γ' → by (cong succΛ (n₁ γₛ γₑ γ γ' .witness))

tracking : Tm ∙ ω (Π {∙} ω (Nat {∙}) (Nat {∙ ▷[ z ] (Nat {∙})}))
  → Σ[ fₛ ∈ (ℕ → ℕ) ]
    Σ[ fₑ ∈ Λ ]
    (∀ aₛ aₑ → (aₑ ≡ embed-nat aₛ) true → ((fₑ ＠ aₑ) ≡ embed-nat (fₛ aₛ)) true)
tracking (fₛ , fₑ , f₀ , f₁) = fₛ tt , fₑ tt , λ aₛ aₑ → f₁ tt tt tt tt aₛ aₑ tt

noninterference : Tm ∙ ω (Π {∙} z (Nat {∙}) (Nat {∙ ▷[ z ] (Nat {∙})}))
  → Σ[ fₛ ∈ (ℕ → ℕ) ]
    Σ[ fₑ ∈ Λ ]
    Σ[ xₛ ∈ ℕ ]
    ((∀ aₛ → (fₛ aₛ ≡ xₛ) true) × (fₑ ≡ embed-nat xₛ) true)
noninterference (fₛ , fₑ , f₀ , f₁) =
  fₛ tt , fₑ tt , fₛ tt 0
  , (λ n →
    let by pn = f₁ tt tt tt tt n tt in
    let by p0 = f₁ tt tt tt tt 0 tt in by (embed-nat-inj _ _ (trans (sym pn) p0)))
  , f₁ tt tt tt tt 0 tt

