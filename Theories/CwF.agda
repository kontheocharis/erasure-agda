{-# OPTIONS --type-in-type #-}
module Theories.CwF where

open import Agda.Primitive
open import Utils

record CwF-sorts : Set where
  field
    -- Sorts
    Con : Set
    Sub : Con → Con → Set
    Ty : Con → Set
    Tm : ∀ Γ → Ty Γ → Set

module in-CwF-sorts (s : CwF-sorts) where
  open CwF-sorts s
  variable
    Γ Δ Θ : Con
    σ τ ρ : Sub _ _
    A B C : Ty _
    t u v : Tm _ _

  record CwF-core : Set where
    field
      id : Sub Γ Γ
      _∘_ : (σ : Sub Δ Θ) → (τ : Sub Γ Δ) → Sub Γ Θ
      assoc : ρ ∘ (σ ∘ τ) ≡ (ρ ∘ σ) ∘ τ
      ∘id : id ∘ σ ≡ σ
      id∘ : σ ∘ id ≡ σ

      ∙ : Con
      ε : Sub Γ ∙
      ∃!ε : ε {Γ} ≡ σ
    
      _[_]T : (A : Ty Δ) → (σ : Sub Γ Δ) → Ty Γ
      _[_] : (t : Tm Δ A) → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
      [id]T : A [ id ]T ≡ A
      [id] : t [ id ] ≡[ cong (Tm Γ) [id]T ] t
      [∘]T : A [ σ ∘ τ ]T ≡ (A [ σ ]T) [ τ ]T
      [∘] : t [ σ ∘ τ ] ≡[ cong (Tm Γ) [∘]T ] (t [ σ ]) [ τ ]
  
    coeTm : A ≡ B → Tm Γ A → Tm Γ B
    coeTm p t = subst (Tm _) p t
      
    field
      -- Context extension
      _▷_ : (Γ : Con) → (A : Ty Γ) → Con
      p : Sub (Γ ▷ A) Γ
      q : Tm (Γ ▷ A) (A [ p ]T)
      _,,_ : (σ : Sub Γ Δ) → (t : Tm Γ (A [ σ ]T)) → Sub Γ (Δ ▷ A)
      ,∘ : (σ ,, t) ∘ ρ ≡ (σ ∘ ρ) ,, coeTm (sym [∘]T) (t [ ρ ])
      p,q : p {Γ} {A} ,, q ≡ id
      p∘, : p ∘ (σ ,, t) ≡ σ
      q[,] : q [ σ ,, t ] ≡[ cong (Tm Γ) (trans (sym [∘]T) (cong (A [_]T) p∘,)) ] t


    ⟨_⟩ : (t : Tm Γ A) → Sub Γ (Γ ▷ A)
    ⟨ t ⟩ = id ,, (t [ id ])

    _⁺ : (σ : Sub Γ Δ) → Sub (Γ ▷ (A [ σ ]T)) (Δ ▷ A)
    σ ⁺ = (σ ∘ p) ,, subst (Tm _) (sym [∘]T) q
  

  module in-CwF-core (c : CwF-core) where
    open CwF-core c

    record Π-structure  : Set where
      field
        Π : (A : Ty Γ) → (B : Ty (Γ ▷ A)) → Ty Γ
        Π[] : (Π A B) [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ⁺ ]T)

        lam : (f : Tm (Γ ▷ A) B) → Tm Γ (Π A B)
        lam[] : (lam t) [ σ ] ≡[ cong (Tm _) Π[] ] lam (t [ σ ⁺ ])

        ap : (f : Tm Γ (Π A B)) → Tm (Γ ▷ A) B

        Πβ : ap (lam t) ≡ t
        Πη : lam (ap t) ≡ t

      _⇒_ : Ty Γ → Ty Γ → Ty Γ
      A ⇒ B = Π A (B [ p ]T)

    record U-small-structure : Set where
      field
        U : Ty Γ
        U[] : U [ σ ]T ≡ U

        El : (t : Tm Γ U) → Ty Γ
        El[] : (El t) [ σ ]T ≡ El (subst (Tm _) U[] (t [ σ ]))

      _[_]U : (t : Tm Δ U) → (σ : Sub Γ Δ) → Tm Γ U
      _[_]U t σ = coeTm U[] (t [ σ ])

      _⁺U : (σ : Sub Γ Δ) → Sub (Γ ▷ El (t [ σ ]U)) (Δ ▷ El t)
      σ ⁺U = ((σ ∘ p) ,, subst (Tm _) (trans (cong (_[ p ]T) (sym El[])) (sym [∘]T)) q)

      TmU : ∀ Γ → Tm Γ U → Set
      TmU Γ t = Tm Γ (El t)

      _[_]u : (a : TmU Δ t) → (σ : Sub Γ Δ) → TmU Γ (t [ σ ]U)
      _[_]u a σ = coeTm El[] (a [ σ ])

      _▷U_ : (Γ : Con) → Tm Γ U → Con
      Γ ▷U t = Γ ▷ El t

    record U-big-structure (u-small : U-small-structure) : Set where
      open U-small-structure u-small
      field
        code : (A : Ty Γ) → Tm Γ U
        code[] : (code A) [ σ ] ≡[ cong (Tm _) U[] ] code (A [ σ ]T)

        El-code : El (code A) ≡ A
        code-El : code (El t) ≡ t

    record ΠU-structure (univ : U-small-structure) : Set where
      open U-small-structure univ
      field
        ΠU : (t : Tm Γ U) → (u : Tm (Γ ▷U t) U) → Tm Γ U
        ΠU[] : (ΠU t u) [ σ ]U ≡ ΠU (t [ σ ]U) (u [ σ ⁺U ]U)

        lamU : (f : TmU (Γ ▷U t) u) → TmU Γ (ΠU t u)
        lamU[] : (lamU t) [ σ ]u ≡[ cong (TmU _) ΠU[] ] lamU (t [ σ ⁺U ]u)

        apU : (f : TmU Γ (ΠU t u)) → TmU (Γ ▷U t) u

        ΠβU : apU (lamU t) ≡ t
        ΠηU : lamU (apU t) ≡ t



