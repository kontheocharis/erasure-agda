{-# OPTIONS --allow-unsolved-metas #-}
module Theories.LC where

open import Agda.Primitive
open import Utils
open import Mode
open import Data.Nat using (ℕ; suc)

private
  variable
    ℓ ℓ' ℓp ℓty ℓtm : Level

record LC : Set (lsuc ℓ) where
  field
    Λ : Set ℓ
    lambda : (f : Λ → Λ) → Λ
    apply : Λ → Λ → Λ
    beta : ∀ f x → apply (lambda f) x ≡ f x
    eta : ∀ f → lambda (λ x → apply f x) ≡ f

  _$_ : Λ → Λ → Λ
  x $ y = apply x y

  infixl 5 _$_

  syntax lambda (λ x → t) = ƛ x ⇒ t
    
  zeroΛ : Λ
  zeroΛ = ƛ z ⇒ ƛ s ⇒ z

  succΛ : Λ → Λ
  succΛ n = ƛ z ⇒ ƛ s ⇒ (s $ n $ (n $ z $ s))

  id : Λ
  id = ƛ x ⇒ x

  recΛ : Λ → (Λ → Λ → Λ) → Λ → Λ
  recΛ zr su n = n $ zr $ (ƛ k ⇒ ƛ sk ⇒ su k sk)

  recΛβ-zero : ∀ {zr su} → recΛ zr su zeroΛ ≡ zr
  recΛβ-zero {zr} {su} =  {!   !}
    --   recΛ zr su zeroΛ
    -- ≡⟨⟩
    --   ((ƛ z ⇒ ƛ s ⇒ z) $ zr $ (ƛ k ⇒ ƛ sk ⇒ su k sk))
    -- ≡⟨ (λ i → (beta (λ z → ƛ s ⇒ z) zr i) $ (ƛ k ⇒ ƛ sk ⇒ su k sk)) ⟩
    --   ((ƛ s ⇒ zr) $ (ƛ k ⇒ ƛ sk ⇒ su k sk))
    -- ≡⟨ (λ i → (beta (λ s → zr) (ƛ k ⇒ ƛ sk ⇒ su k sk) i)) ⟩
    --   zr
    -- ∎

  recΛβ-succ : ∀ {zr su n} → recΛ zr su (succΛ n) ≡ su n (recΛ zr su n)
  recΛβ-succ {zr} {su} {n} = {!   !}
    --   recΛ zr su (succΛ n)
    -- ≡⟨⟩
    --   ((ƛ z ⇒ ƛ s ⇒ (s $ n $ (n $ z $ s))) $ zr $ (ƛ k ⇒ ƛ sk ⇒ su k sk))
    -- ≡⟨ (λ i → (beta (λ z → ƛ s ⇒ (s $ n $ (n $ z $ s))) zr i) $ (ƛ k ⇒ ƛ sk ⇒ su k sk)) ⟩
    --   ((ƛ s ⇒ (s $ n $ (n $ zr $ s))) $ (ƛ k ⇒ ƛ sk ⇒ su k sk))
    -- ≡⟨ beta _ _ ⟩
    --   ((ƛ k ⇒ ƛ sk ⇒ su k sk) $ n $ (n $ zr $ (ƛ k ⇒ ƛ sk ⇒ su k sk)))
    -- ≡⟨ (λ i → beta (λ k → ƛ sk ⇒ su k sk) n i $ (n $ zr $ (ƛ k ⇒ ƛ sk ⇒ su k sk))) ⟩
    --   ((ƛ sk ⇒ su n sk) $ (n $ zr $ (ƛ k ⇒ ƛ sk ⇒ su k sk)))
    -- ≡⟨ beta _ _ ⟩ 
    --   su n (recΛ zr su n)
    -- ∎

  embed-nat : ℕ → Λ
  embed-nat ℕ.zero = zeroΛ
  embed-nat (suc x) = succΛ (embed-nat x)