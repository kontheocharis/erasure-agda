{-# OPTIONS --type-in-type #-}
module Models.FO.FamSet where

open import Data.Product
open import Data.Product.Properties
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding (zero)
open import Data.Vec

open import Utils hiding (⊤; ⊥)
open import Theories.CwFwE
open import Mode

module _ where
  open CwFwE-sorts
  open in-CwFwE-sorts
  open CwFwE-core
  open in-CwFwE-core

  fam-s : CwFwE-sorts
  fam-s .Con = Σ[ Γ₀ ∈ Set ] (Γ₀ → Set)
  fam-s .Sub (Γ₀ , Γ₁) (Δ₀ , Δ₁) = Σ[ σ₀ ∈ (Γ₀ → Δ₀) ] (∀ γ → Γ₁ γ → Δ₁ (σ₀ γ))  
  fam-s .Ty (Γ₀ , Γ₁) =  Σ[ A₀ ∈ (Γ₀ → Set) ] (∀ γ → A₀ γ → Set)
  fam-s .Tm (Γ₀ , Γ₁) ω (A₀ , A₁) = Σ[ a₀ ∈ ((γ : Γ₀) → A₀ γ) ] (∀ γ → (γ' : Γ₁ γ) → A₁ γ (a₀ γ))  
  fam-s .Tm (Γ₀ , Γ₁) z (A₀ , A₁) = (γ : Γ₀) → A₀ γ
  fam-s .#∈ (Γ₀ , Γ₁) = (γ : Γ₀) → Γ₁ γ → ⊥

  fam-c : CwFwE-core fam-s
  fam-c .id = (λ γ → γ) , (λ γ γ' → γ') 
  (fam-c ∘ (σ₀ , σ₁)) (τ₀ , τ₁) = (λ γ → σ₀ (τ₀ γ)) , (λ γ γ' → σ₁ (τ₀ γ) (τ₁ γ γ'))
  fam-c .assoc = refl
  fam-c .∘id = refl
  fam-c .id∘ = refl
  fam-c .∙ = ⊤ , λ z → ⊤
  fam-c .ε = (λ _ → tt) , (λ γ _ → tt)
  fam-c .∃!ε = refl
  (fam-c [ A₀ , A₁ ]T) (σ₀ , σ₁) = (λ γ → A₀ (σ₀ γ)) , (λ γ a → A₁ (σ₀ γ) a)
  fam-c ._[_] {i = ω} (t₀ , t₁) (σ₀ , σ₁) = (λ γ → t₀ (σ₀ γ)) , (λ γ γ' → t₁ (σ₀ γ) (σ₁ γ γ'))
  fam-c ._[_] {i = z} t₀ (σ₀ , σ₁) = λ γ → t₀ (σ₀ γ)
  fam-c .[id]T = refl
  fam-c .[id] {i = z} = refl
  fam-c .[id] {i = ω} = refl
  fam-c .[∘]T = refl
  fam-c .[∘] {i = z} = refl
  fam-c .[∘] {i = ω} = refl
  (fam-c ▷[ (Γ₀ , Γ₁) ] ω) (A₀ , A₁) = (Σ[ γ ∈ Γ₀ ] A₀ γ) , λ (γ , a) → Σ[ γ' ∈ Γ₁ γ ] A₁ γ a
  (fam-c ▷[ (Γ₀ , Γ₁) ] z) (A₀ , A₁) = (Σ[ γ ∈ Γ₀ ] A₀ γ) , λ (γ , a) → Γ₁ γ
  fam-c .p {i = ω} = (λ (γ , a) → γ) , (λ γa (γ' , a') → γ')
  fam-c .p {i = z} = (λ (γ , a) → γ) , (λ γa γ' → γ')
  fam-c .q {i = ω} = (λ (γ , a) → a) , (λ γa (γ' , a') → a')
  fam-c .q {i = z} = λ (γ , a) → a
  fam-c ._,,_ {i = ω} (σ₀ , σ₁) (t₀ , t₁)
    = (λ γa → σ₀ γa , t₀ γa) , (λ γa γ'a' → σ₁ γa γ'a' , t₁ γa γ'a')
  fam-c ._,,_ {i = z} (σ₀ , σ₁) t₀
    = (λ γa → σ₀ γa , t₀ γa) , (λ γa γ'a' → σ₁ γa γ'a')
  fam-c .,∘ {i = z} = refl
  fam-c .,∘ {i = ω} = refl
  fam-c .p,q {i = z} = refl
  fam-c .p,q {i = ω} = refl
  fam-c .p∘, {i = z} = refl
  fam-c .p∘, {i = ω} = refl
  fam-c .q[,] {i = z} = refl
  fam-c .q[,] {i = ω} = refl

  (fam-c [ t ]#) σ γ x = t (σ .proj₁ γ) (σ .proj₂ γ x) 
  fam-c .[id]# = refl
  fam-c .[∘]# = refl
  (fam-c ▷#) (Γ₀ , Γ₁) = Γ₀ , (λ _ → ⊥)
  fam-c .p# = (λ z₁ → z₁) , λ γ ()
  fam-c .q# γ x = x
  (fam-c ,# σ) π = σ .proj₁ , π
  fam-c .,#∘ = refl
  fam-c .p,#q = refl
  fam-c .p∘,# {π = π} = Σ≡ refl (funext (λ γ → funext λ γ' → ⊥-elim-prop (π γ γ'))) 
  fam-c .q[,#] = refl
  fam-c .↓ x γ = x .proj₁ γ
  fam-c .↑ x = x , λ γ ()
  fam-c .↑↓ {t = t} = Σ≡ refl (funext λ x → funext λ ()) 
  fam-c .↓↑ = refl
  fam-c .↓[] = refl
  fam-c .pz∘⁺≡⁺∘pz' = refl


  open Π-structure

  fam-Π : Π-structure fam-s fam-c
  fam-Π .Π ω (A₀ , A₁) (B₀ , B₁) =
    (λ γ → (a : A₀ γ) → B₀ (γ , a))
    , λ γ f → ∀ a → A₁ γ a → B₁ (γ , a) (f a)
  fam-Π .Π i (A₀ , A₁) (B₀ , B₁) =
    (λ γ → (a : A₀ γ) → B₀ (γ , a))
    , λ γ f → ∀ a → B₁ (γ , a) (f a)
  fam-Π .Π[] {z} = refl
  fam-Π .Π[] {ω} = refl
  fam-Π .lam {i = z} f = (λ γ a → f .proj₁ (γ , a)) , (λ γ γ' a → f .proj₂ (γ , a) γ')
  fam-Π .lam {i = ω} f = (λ γ a → f .proj₁ (γ , a)) ,
                          (λ γ γ' a z₁ → f .proj₂ (γ , a) (γ' , z₁))
  fam-Π .lam[] {z} = refl
  fam-Π .lam[] {ω} = refl
  fam-Π .ap {i = z} f = (λ γ → f .proj₁ (γ .proj₁) (γ .proj₂)) ,
                         (λ γ γ' → f .proj₂ (γ .proj₁) γ' (γ .proj₂))
  fam-Π .ap {i = ω} f = (λ γ → f .proj₁ (γ .proj₁) (γ .proj₂)) ,
                         (λ γ γ' → f .proj₂ (γ .proj₁) (γ' .proj₁) (γ .proj₂) (γ' .proj₂))
  fam-Π .Πβ {z} = refl
  fam-Π .Πβ {ω} = refl
  fam-Π .Πη {z} = refl
  fam-Π .Πη {ω} = refl


  open U-structure

  fam-U : U-structure fam-s fam-c
  fam-U .U = (λ γ → Σ[ A ∈ Set ] (A → Set)) , λ γ a → ⊤
  fam-U .U[] = refl
  fam-U .El t₀ = (λ γ → t₀ γ .proj₁) , λ γ a → t₀ γ .proj₂ a
  fam-U .El[] = refl
  fam-U .code (A₀ , A₁) = λ γ → A₀ γ , A₁ γ
  fam-U .code[] = refl
  fam-U .El-code = refl
  fam-U .code-El = refl

  open Π'-structure

  fam-Π' : Π'-structure fam-s fam-c
  fam-Π' .Π' (A₀ , A₁) (B₀ , B₁) = 
    (λ γ → (a : A₀ γ) → B₀ (γ , a))
    ,  λ γ f → ∀ a → (a' : A₁ γ a) → B₁ (γ , a) (f a)
  fam-Π' .Π'[] = refl
  fam-Π' .lam' = λ f →
                    (λ γ a → f .proj₁ (γ , a)) ,
                    (λ γ γ' a a' → f .proj₂ (γ , a) (γ' , a'))
  fam-Π' .lam'[] = refl
  fam-Π' .ap' = λ f →
                   (λ γ → f .proj₁ (γ .proj₁) (γ .proj₂)) ,
                   (λ γ γ' → f .proj₂ (γ .proj₁) (γ' .proj₁) (γ .proj₂) (γ' .proj₂))
  fam-Π' .Πβ' = refl
  fam-Π' .Πη' = refl

-- open CwFwE-sorts fam-s
-- open in-CwFwE-sorts fam-s
-- open CwFwE-core fam-c
-- open in-CwFwE-core fam-c
-- -- open Π-structure fam-Π
-- open U-structure fam-HSU

-- -- Phase separator (yoneda of base)
-- ϕ : Ty Γ
-- ϕ = (λ γ → ⊤) , λ γ a → ⊥

-- -- ϕ is a proposition
-- ϕ-prop : (t u : Tm Γ (ϕ {Γ})) → t ≡ u
-- ϕ-prop t u = refl

-- -- Exponentiating by ϕ isolates the base
-- exp-ϕ : {A : Ty Γ} → Tm Γ (_⇒_ {Γ} (ϕ {Γ}) A) ≃ (∀ γ → A .proj₁ γ)
-- exp-ϕ .to (t₀ , t₁) = λ γ → t₀ γ tt
-- exp-ϕ .from t = (λ γ a → t γ) , λ γ γ' a ()
-- exp-ϕ .to-from = λ x → refl
-- exp-ϕ .from-to (t₀ , t₁) = Σ-≡,≡→≡ (refl , funext λ x → funext λ y → funext  λ z → funext λ ()) 

-- open Π-structure
