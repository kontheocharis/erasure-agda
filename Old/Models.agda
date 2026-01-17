{-# OPTIONS  --cubical #-}
module Models where

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (zero)

open import Theories
open import Gluing

data ⊤ : Prop where
    tt : ⊤

data ⊥ : Prop where

exfalso : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
exfalso ()

open ITT 
open ITT-sorts 
open ITT-ctors



-- LC model of ITT
-- Erases irrelevant stuff.

-- Fam(Set) model of ITT
--
-- This is in a sense the "standard model" of ITT.
--
-- Since we need to produce a second-order model of ITT, we must work in the
-- internal language of Fam(Set). Luckily, this is (equivalent to) a presheaf
-- category, specifically the functor category I → Set where I is the 'walking
-- arrow'/interval category. Equivalently it is the arrow category Set^→.
-- Presheaf categories have an interpretation of dependent type theory, so we
-- can just use reuse Agda's. Additionally in this category there is also a
-- special object `P` which is (1, λ _ → 0) in Fam(Set). Any two inhabitants of
-- P are equal. If we take functions out of this `P → A`, it amounts to only
-- looking at the 'set' component of A and ignoring the 'family' component.

-- To that end, we interpret the relevant fragment of ITT using families of sets,
-- and the irrelevant fragment using empty families of sets.

module FamSet-ITT (P : Prop) where
  open ITT 
  open ITT-sorts 
  open ITT-ctors

  postulate
    SetE : Set2
    E : SetE → Set1
    ΠE : (A : SetE) → (E A → SetE) → SetE
    λE : ∀ {A B} → ((a : E A) → E (B a)) → E (ΠE A B)
    apE : ∀ {A B} → E (ΠE A B) → ((a : E A) → E (B a))
    βE : ∀ {A B x} → λE {A} {B} (apE x) ≡ x
    ηE : ∀ {A B f x} → apE {A} {B} (λE f) x ≡ f x

  i-sorts : ITT-sorts {lzero} {lsuc (lsuc lzero)} {lsuc lzero}
  i-sorts .# = P
  i-sorts .Ty = Set1
  i-sorts .Tm z A = P → A
  i-sorts .Tm ω A = A
  [ i-sorts ] x = x
  (↑[ i-sorts ] x) x₁ = x₁ x
  [↑[ i-sorts ]]-id = refl
  ↑[[ i-sorts ]]-id = refl

  i-ctors : ITT-ctors i-sorts
  i-ctors .Π z A B = (a : P → A) → B a
  i-ctors .Π ω A B = (a : A) → B (λ _ → a)
  i-ctors .lam {z} f = f
  i-ctors .lam {ω} f = f
  i-ctors .app {z} x a = x a
  i-ctors .app {ω} x a = x a
  i-ctors .lam-app {z} = refl
  i-ctors .lam-app {ω} = refl
  i-ctors .app-lam {z} = refl
  i-ctors .app-lam {ω} = refl
  i-ctors .U = Set
  i-ctors .El X = Lift ((p : P) → X p)
  i-ctors .Nat = Lift ℕ 
  i-ctors .zero = lift ℕ.zero
  i-ctors .succ n = lift (suc (n .lower))
  i-ctors .elim-Nat X ze su (lift n) = elim
    {A = λ k → X (λ _ → lift k)}
    ze (λ k pk → su (lift k) pk) n 
  i-ctors .elim-Nat-zero = refl
  i-ctors .elim-Nat-succ = refl

  i : ITT {lzero} {lsuc (lsuc lzero)} {lsuc lzero}
  i .sorts = i-sorts
  i .ctors = i-ctors



-- Code extraction correctness model
module code-extraction-correct-ITT {ℓ} {ℓ'} where
  open LC
  open ITT 
  open ITT-sorts 
  open ITT-ctors

  postulate
    synE : Prop -- open (code Extraction) from the gluing
    synS : Prop -- open (Standard model) from the gluing
    ϕ : Prop   -- open from the base topos which is Set→

  postulate
    SE : synE → ITT {lzero} {ℓ} {ℓ'}
    SS : synS → ITT {lzero} {ℓ} {ℓ'}

  postulate
    ϕE# : (e : synE) → ϕ → SE e .#
    ϕS# : (s : synS) → ϕ → SS s .#
  

--   -- here we have the syntax of ITT that restricts to the irrelevant fragment.
--   -- In other words, when P is true, then # is true in the syntax. (Sterling and
--   -- Harper, sec 3.3)
--   postulate
--     disjoint : ϕΓ → ϕid → ⊥
--     l : ∀ {ℓ} → ϕΓ → LC {ℓ}

--   -- This is the code extraction model of ITT
--   li : ∀ {ℓ} {ℓ'} → ϕΓ → ITT {lzero} {ℓ} {ℓ'}
--   li p = LC-ITT.i (l p) 

--   -- We are gonna make a displayed model over this one
  
--   i-sorts : [ ITT-sorts {lzero} {lsuc (lsuc lzero)} {lsuc lzero} ∣ p ∈ ϕΓ ↪ li p .sorts ]
--   i-sorts .fst .# = ϕid
--   i-sorts .fst .Ty = [ Set1 ∣ p ∈ ϕΓ ↪ l p .Λ ]
--   i-sorts .fst .Tm z A = ϕid → A .fst
--   i-sorts .fst .Tm ω A = A .fst
--   [ i-sorts .fst ] x x₁ = x x₁
--   i-sorts .fst .↑[_]_ = λ z₁ z₂ → z₂ z₁
--   [↑[ i-sorts .fst ]]-id = refl
--   ↑[[ i-sorts .fst ]]-id = refl
--   i-sorts .snd p i .# = {! !}
--   i-sorts .snd p i .Ty = {!!}
--   i-sorts .snd p i .Tm = {!!}
--   [ i-sorts .snd p i ] = {!!}
--   i-sorts .snd p i .↑[_]_ = {!!}
--   [↑[ i-sorts .snd p i ]]-id = {!!}
--   ↑[[ i-sorts .snd p i ]]-id = {!!}

--   i-ctors : [ ITT-ctors (* i-sorts) ∣ p ∈ ϕΓ ↪ *coe p ITT-ctors i-sorts (li p .ctors)  ]
--   i-ctors .fst .Π z A B = G[ x ∈ (λ p → l p .Λ) ]
--     [ ((a : ϕid → A .fst) → (B a) .fst)
--       ∣ p ∈ ϕΓ ↪ (λ a → give p (λ p → l p .Λ) (B a) (x p)) ]
--       , λ p → G-collapses p 
--   i-ctors .fst .Π ω A B = G[ x ∈ (λ p → l p .Λ) ]
--     [ ((a : A .fst) → (B (λ _ → a)) .fst)
--       ∣ p ∈ ϕΓ ↪ (λ a → give p (λ p → l p .Λ) (B (λ _ → a)) (l p .apply (x p) (give' p (λ p → l p .Λ) A a))) ]
--       , λ p → G-collapses p 
--   i-ctors .fst .lam {z} {A} {X} f = ((λ p → give' p (λ p → l p .Λ)
--     (X (λ x → exfalso (disjoint p x)))
--     (f (λ x → exfalso (disjoint p x))))) ,  f , {! correct!}
--   i-ctors .fst .lam {ω} {A} {X} f = (λ p → l p .lambda (λ x →  give' p (λ p → l p .Λ)
--     (X (λ _ → give p (λ p → l p .Λ) A x))
--     (f (give p (λ p → l p .Λ) A x))))
--     ,  f , {! correct!}
--   i-ctors .fst .app {z} f x = f .snd .fst x
--   i-ctors .fst .app {ω} f x = f .snd .fst x
--   i-ctors .fst .lam-app {j = z} = {! ?!}
--   i-ctors .fst .lam-app {j = ω} = {! ?!}
--   i-ctors .fst .app-lam {z} = refl
--   i-ctors .fst .app-lam {ω} = refl
--   i-ctors .fst .U = [ Set ∣ p ∈ ϕΓ ↪ l p .Λ ] , {! correct!} 
--   i-ctors .fst .El X = (Lift ((p : ϕid) → X p .fst)) ,  λ p → {! correct!}
--   i-ctors .fst .Nat =  G[ n ∈ (λ p → l p .Λ) ] (ϕΓ ⋆ (Σ[ k ∈ ℕ ] (ϕid ⋆ (n ≡ (λ p → embed-nat (l p) k))))) , λ x → G-collapses x
--   i-ctors .fst .zero = (λ p → zeroΛ (l p)) , η ((0 , η refl))
--   i-ctors .fst .succ n = (λ p → succΛ (l p) (n .fst p))
--     , do
--       n' ← n .snd
--       η ((suc (n' .fst) , do n'' ← n' .snd ; η (propFunExt (λ p → cong (λ k → succΛ (l p) (k p)) n''))))
--   i-ctors .fst .elim-Nat P z' s' (n , nope p) = give p (λ p → l p .Λ) (P _)
--     (recΛ (l p) (give' p (λ p → l p .Λ) (P _) z')
--       (λ k pk → give' p (λ p → l p .Λ) (P _)
--         (s' ((λ p → k) , nope p) (give p (λ p → l p .Λ) (P _) pk)))
--       (n p))
--   i-ctors .fst .elim-Nat P z' s' (n , η (ℕ.zero , np)) = transport (λ i → P {! !} .fst) z' 
--   i-ctors .fst .elim-Nat P z' s' (n , η (suc n' , np)) = {! !}
--   i-ctors .fst .elim-Nat P z' s' (n , trivial p i) = {!!}
--   i-ctors .fst .elim-Nat-zero = {!!}
--   i-ctors .fst .elim-Nat-succ = {!!}
--   i-ctors .snd = {!!}

--   i : [ ITT {lzero} {lsuc (lsuc lzero)} {lsuc lzero} ∣ ϕΓ ↪ li ]
--   i .fst .sorts = * i-sorts
--   i .fst .ctors = * i-ctors 
--   i .snd ψ i .sorts = (i-sorts ＠ ψ) i 
--   i .snd ψ i .ctors = {! !}



--   module noninterference (f : i-sorts .fst .Tm ω (i-ctors .fst .Π z (i-ctors .fst .Nat) (λ _ → i-ctors .fst .Nat))) where

--     sem : (ϕΓ ⋆ ℕ) → (ϕΓ ⋆ ℕ)
--     sem n = do
--       let (fΛ , f , p) = f
--       n' ← n
--       let x = f λ p → (λ q → embed-nat (l q) n') , η (n' , η refl)
--       x' ← x .snd
--       η (x' .fst)

--     noninterference : ϕΓ ⋆ (Σ[ n ∈ ℕ ] (∀ p → f .fst p ≡ embed-nat (l p) n))
--     noninterference = do
--       let (fΛ , f , p) = f
--       let (x , xp) = f  λ q →  {! ? , ?!}
--       xp' ← xp
--       η ( xp' .fst , {! !})

  
