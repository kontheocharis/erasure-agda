{-# OPTIONS --type-in-type #-}
module Theories.QCwF where

open import Agda.Primitive
open import Utils
open import Mode

record QCwF-sorts : Set where
  field
    -- Sorts
    Con : Set
    Conω : Con → Set

    Sub : Con → Con → Set
    Subω : ∀ {Γ Δ} → Conω Γ → Conω Δ → Sub Γ Δ → Set

    Ty : Con → Set

    Tm : ∀ Γ → Ty Γ → Set
    Tmω : ∀ {Γ} → Conω Γ → (A : Ty Γ) → Tm Γ A → Set

module in-QCwF-sorts (s : QCwF-sorts) where
  open QCwF-sorts s
  variable
    Γ Δ Θ : Con
    Γω Δω Θω : Conω _
    σ τ ρ : Sub _ _
    σω τω ρω : Subω _ _ _
    A B C : Ty _
    t u v : Tm _ _
    tω uω vω : Tmω _ _ _

  record QCwF-core : Set where
    field
      id : Sub Γ Γ
      _∘_ : (σ : Sub Δ Θ) → (τ : Sub Γ Δ) → Sub Γ Θ
      assoc : ρ ∘ (σ ∘ τ) ≡ (ρ ∘ σ) ∘ τ
      ∘id : id ∘ σ ≡ σ
      id∘ : σ ∘ id ≡ σ

      idω : Subω Γω Δω id
      _∘ω_ : (σω : Subω Δω Θω σ) → (τω : Subω Γω Δω τ) → Subω Γω Θω (σ ∘ τ)
      assocω : ρω ∘ω (σω ∘ω τω) ≡[ cong (Subω _ _) assoc ] (ρω ∘ω σω) ∘ω τω
      ∘idω : idω ∘ω σω ≡[ cong (Subω _ _) ∘id ] σω
      id∘ω : σω ∘ω idω ≡[ cong (Subω _ _) id∘ ] σω

      ∙ : Con
      ε : Sub Γ ∙
      ∃!ε : ε {Γ} ≡ σ

      ∙ω : Conω ∙
      εω : Subω Γω ∙ω ε
      ∃!εω : εω ≡[ cong (Subω _ _) ∃!ε ] σω
    
      _[_]T : (A : Ty Δ) → (σ : Sub Γ Δ) → Ty Γ
      _[_] : (t : Tm Δ A) → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)

      [id]T : A [ id ]T ≡ A
      [id] : t [ id ] ≡[ cong (Tm Γ) [id]T ] t
      [∘]T : A [ σ ∘ τ ]T ≡ (A [ σ ]T) [ τ ]T
      [∘] : t [ σ ∘ τ ] ≡[ cong (Tm Γ) [∘]T ] (t [ σ ]) [ τ ]

      _[_]ω : (tω : Tmω Δω A t) → (σω : Subω Γω Δω σ) → Tmω Γω (A [ σ ]T) (t [ σ ])
      [id]ω : tω [ idω ]ω ≡[  cong2 (Tmω _) [id]T [id] ] tω
      [∘]ω : tω [ σω ∘ω τω ]ω ≡[ cong2 (Tmω _) [∘]T [∘] ] (tω [ σω ]ω) [ τω ]ω
  
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

      _▷ω_ : (Γω : Conω Γ) → (A : Ty Γ) → Conω (Γ ▷ A)
      pω : Subω (Γω ▷ω A) Γω p
      qω : Tmω (Γω ▷ω A) (A [ p ]T) q
      _,,ω_ : (σω : Subω Γω Δω σ) → (tω : Tmω Γω (A [ σ ]T) t) → Subω Γω (Δω ▷ω A) (σ ,, t)
      ,∘ω : (σω ,,ω tω) ∘ω ρω ≡[ cong (Subω _ _) ,∘ ]
            (σω ∘ω ρω) ,,ω coe (cong2 (Tmω _) (sym [∘]T) refl) (tω [ ρω ]ω)
      p,qω : pω {Γω = Γω} {A = A} ,,ω qω ≡[ cong (Subω _ _) p,q ] idω
      p∘,ω : pω ∘ω (σω ,,ω tω) ≡[ cong (Subω _ _) p∘, ] σω
      q[,]ω : qω [ σω ,,ω tω ]ω ≡[ cong2 (Tmω _) (trans (sym [∘]T) (cong (A [_]T) p∘,)) q[,] ]
              tω

      _▷z_ : (Γω : Conω Γ) → (A : Ty Γ) → Conω (Γ ▷ A)
      pz : Subω (Γω ▷z A) Γω p
      _,,z_ : (σω : Subω Γω Δω σ) → (t : Tm Γ (A [ σ ]T)) → Subω Γω (Δω ▷z A) (σ ,, t)
      ,∘z : (σω ,,z t) ∘ω ρω ≡[ cong (Subω _ _) ,∘ ]
            (σω ∘ω ρω) ,,z coe (cong (Tm _) (sym [∘]T)) (t [ ρ ])
      p,qz : pz {Γω = Γω} {A = A} ,,z q ≡[ cong (Subω _ _) p,q ] idω
      p∘,z : pz ∘ω (σω ,,z t) ≡[ cong (Subω _ _) p∘, ] σω

    ⟨_⟩ : (t : Tm Γ A) → Sub Γ (Γ ▷ A)
    ⟨ t ⟩ = id ,, (t [ id ])

    ⟨_⟩ω : (tω : Tmω Γω A t) → Subω Γω (Γω ▷ω A) ⟨ t ⟩
    ⟨ tω ⟩ω = idω ,,ω (tω [ idω ]ω)

    ⟨_⟩z : (t : Tm Γ A) → Subω Γω (Γω ▷z A) ⟨ t ⟩
    ⟨ t ⟩z = idω ,,z (t [ id ])

    _⁺ : (σ : Sub Γ Δ) → Sub (Γ ▷ (A [ σ ]T)) (Δ ▷ A)
    σ ⁺ = (σ ∘ p) ,, subst (Tm _) (sym [∘]T) q

    _⁺ω : (σω : Subω Γω Δω σ) → Subω (Γω ▷ω (A [ σ ]T)) (Δω ▷ω A) (σ ⁺)
    σω ⁺ω = (σω ∘ω pω) ,,ω coe (cong2 (Tmω _) (sym [∘]T) refl) qω

    _⁺z : (σω : Subω Γω Δω σ) → Subω (Γω ▷z (A [ σ ]T)) (Δω ▷z A) (σ ⁺)
    σω ⁺z = (σω ∘ω pz) ,,z coe (cong (Tm _) (sym [∘]T)) q

  module in-QCwF-core (c : QCwF-core) where
    open QCwF-core c

    record Π-structure : Set where
      field
        Π : Mode → (A : Ty Γ) → (B : Ty (Γ ▷ A)) → Ty Γ
        Π[] : (Π i A B) [ σ ]T ≡ Π i (A [ σ ]T) (B [ σ ⁺ ]T)

        lam : (f : Tm (Γ ▷ A) B) → Tm Γ (Π i A B)
        lam[] : (lam {i = i} t) [ σ ] ≡[ cong (Tm _) Π[] ] lam (t [ σ ⁺ ])

        ap : (f : Tm Γ (Π i A B)) → Tm (Γ ▷ A) B

        Πβ : ap {i = i} (lam t) ≡ t
        Πη : lam {i = i} (ap t) ≡ t

      _⇒_ : Ty Γ → Ty Γ → Ty Γ
      A ⇒ B = Π ω A (B [ p ]T)

    record Πω-structure (Π-s : Π-structure) : Set where
      open Π-structure Π-s
      field
        lamω : (tω : Tmω (Γω ▷ω A) B t) → Tmω Γω (Π ω A B) (lam t)
        lamω[] : (lamω tω) [ σω ]ω ≡[ cong2 (Tmω _) Π[] lam[] ] lamω (tω [ σω ⁺ω ]ω)

        apω : (tω : Tmω Γω (Π ω A B) t) → Tmω (Γω ▷ω A) B (ap t)

        Πβω : apω (lamω tω) ≡[ cong (Tmω _ _) Πβ ] tω
        Πηω : lamω (apω tω) ≡[ cong (Tmω _ _) Πη ] tω


    record U-small-structure : Set where
      field
        U : Ty Γ
        U[] : U [ σ ]T ≡ U

        El : (t : Tm Γ U) → Ty Γ
        El[] : (El t) [ σ ]T ≡ El (subst (Tm _) U[] (t [ σ ]))

    record U-big-structure (u-small : U-small-structure) : Set where
      open U-small-structure u-small
      field
        code : (A : Ty Γ) → Tm Γ U
        code[] : (code A) [ σ ] ≡[ cong (Tm _) U[] ] code (A [ σ ]T)

        El-code : El (code A) ≡ A
        code-El : code (El t) ≡ t



