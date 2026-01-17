module Utils where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Level using (Level; _⊔_; suc)
open import Data.Product
open import Agda.Builtin.Sigma
open import Data.Empty renaming (⊥ to Empty)

private variable
  ℓ ℓ' : Level
  A B : Set ℓ
  x y z w : A

data ⊤ : Prop where
    tt : ⊤

data ⊥ : Prop where

exfalso : ∀ {ℓ} {A : Set ℓ} → ⊥ → A
exfalso ()

exfalso-prop : ∀ {ℓ} {A : Prop ℓ} → ⊥ → A
exfalso-prop ()

⊥-elim-prop : ∀ {w} {Whatever : Prop w} → Empty → Whatever
⊥-elim-prop ()

infix 4 _≡_
data _≡_ {A : Set ℓ} (x : A) : A → Prop ℓ where
  instance refl : x ≡ x

record _≃_ (A : Set ℓ) (B : Set ℓ) : Set ℓ where
  field
    to : A → B
    from : B → A
    to-from : ∀ x → to (from x) ≡ x
    from-to : ∀ x → from (to x) ≡ x

open _≃_ public

record _true (A : Prop ℓ) : Set ℓ where
  constructor by
  field
    witness : A

open _true public

record ΣProp {a b} (A : Prop a) (B : A → Prop b) : Prop (a ⊔ b) where
  constructor _,P_
  field
    fst : A
    snd : B fst

open ΣProp public

{-# BUILTIN REWRITE _≡_ #-}

postulate
  coe : A ≡ B → A → B
  funext : ∀ {B : A → Set ℓ'} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
  propfunext : ∀ {A : Prop ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

opaque
  cong : (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  sym : x ≡ y → y ≡ x
  sym refl = refl

  trans : x ≡ y → y ≡ z → x ≡ z
  trans refl p = p

-- Some fragment of OTT
--
-- We don't add computation rules for the equality type---since it is inductively
-- defined that would break things.
module _ {A : Set ℓ} {B : A → Set ℓ'} {A' : Set ℓ} {B' : A' → Set ℓ'} where
  postulate
    coe-Σ : (Σ A B ≡ Σ A' B') → (ΣProp (A ≡ A') (λ p → ∀ x → B x ≡ B' (coe p x)))
    coe-pair :
      {a : A} {b : B a}
      {p : Σ A B ≡ Σ A' B'}
      → coe p (a , b) ≡ (coe (coe-Σ p .fst) a , coe (coe-Σ p .snd a) b)
    {-# REWRITE coe-pair #-}

    coe-Π : (((a : A) → B a) ≡ ((a : A') → B' a))
      → (ΣProp (A' ≡ A) (λ p → ∀ x → B (coe p x) ≡ B' x))
    coe-lam :
      {f : (a : A) → B a}
      {p : ((a : A) → B a) ≡ ((a : A') → B' a)}
      → coe p f ≡ λ a → coe (coe-Π p .snd _) (f (coe (coe-Π p .fst) a))
    {-# REWRITE coe-lam #-}

-- Adding this as the last rule because it's the most general. Otherwise
-- the typechecker dies
postulate
  coe-eq : coe refl x ≡ x
  {-# REWRITE coe-eq #-}

subst : (P : A → Set ℓ) (p : x ≡ y) → P x → P y
subst P p a = coe (cong P p) a

_∣_≡[_]_ : ∀ {A : Set ℓ} (F : A → Set ℓ') {a} (f : F a) {b} (p : a ≡ b) (g : F b) → Prop ℓ'
_∣_≡[_]_ F f p g = subst F p f ≡ g

infix 4 _≡[_]_

_≡[_]_ : ∀ {A B : Set ℓ} (a : A) (p : A ≡ B) (b : B) → Prop ℓ
_≡[_]_ {A} {B} a p b = coe p a ≡ b

module _ {A : Set ℓ} {B : A → Set ℓ'} where
  Σ≡ : {p₁ p₂ : Σ A B} (p : p₁ .proj₁ ≡ p₂ .proj₁) → subst B p (p₁ .proj₂) ≡ (p₂ .proj₂) → p₁ ≡ p₂
  Σ≡ refl refl = refl

  ≡Σ : {p₁ p₂ : Σ A B} (p : p₁ ≡ p₂)
    → ΣProp (p₁ .proj₁ ≡ p₂ .proj₁) (λ p → subst B p (p₁ .proj₂) ≡ (p₂ .proj₂))
  ≡Σ refl = refl ,P refl

opaque
  dcong : {B : A → Set ℓ} → (f : (a : A) → B a) → (p : x ≡ y) → f x ≡[ cong B p ] f y
  dcong f refl = refl

  cong2 : ∀ {B : A → Set ℓ} {C : Set ℓ'} {x y z w}
      → (f : (a : A) → (b : B a) → C)
      → (p : x ≡ y)
      → (q : z ≡[ cong B p ] w)
      → f x z ≡ f y w
  cong2 f refl refl = refl

  cong2i : ∀ {B : A → Set ℓ} {C : Set ℓ'} {x y z w}
      → (f : {a : A} → (b : B a) → C)
      → (p : x ≡ y)
      → (q : z ≡[ cong B p ] w)
      → f {x} z ≡ f {y} w
  cong2i f refl refl = refl
