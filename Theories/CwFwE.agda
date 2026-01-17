{-# OPTIONS --type-in-type #-}
module Theories.CwFwE where

open import Agda.Primitive
open import Utils
open import Mode

record CwFwE-sorts : Set where
  field
    -- Sorts
    Con : Set
    Sub : Con → Con → Set
    Ty : Con → Set
    #∈ : Con → Set
    Tm : ∀ Γ → Mode → Ty Γ → Set

module in-CwFwE-sorts (s : CwFwE-sorts) where
  open CwFwE-sorts s
  variable
    Γ Δ Θ : Con
    σ τ ρ : Sub _ _
    A B C : Ty _
    t u v : Tm _ _ _
    π : #∈ _

  record CwFwE-core : Set where
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
      _[_] : (t : Tm Δ i A) → (σ : Sub Γ Δ) → Tm Γ i (A [ σ ]T)
      _[_]# : (t : #∈ Δ) → (σ : Sub Γ Δ) → #∈ Γ
      [id]T : A [ id ]T ≡ A
      [id] : t [ id ] ≡[ cong (Tm Γ i) [id]T ] t
      [id]# : π [ id ]# ≡ π
      [∘]T : A [ σ ∘ τ ]T ≡ (A [ σ ]T) [ τ ]T
      [∘] : t [ σ ∘ τ ] ≡[ cong (Tm Γ i) [∘]T ] (t [ σ ]) [ τ ]
      [∘]# : π [ σ ∘ τ ]# ≡ (π [ σ ]#) [ τ ]#
  
    coeTm : A ≡ B → Tm Γ i A → Tm Γ i B
    coeTm p t = subst (Tm _ _) p t
      
    field
      -- Context extension for terms
      _▷[_]_ : (Γ : Con) → Mode → (A : Ty Γ) → Con
      p : Sub (Γ ▷[ i ] A) Γ
      q : Tm (Γ ▷[ i ] A) i (A [ p ]T)
      _,,_ : (σ : Sub Γ Δ) → (t : Tm Γ i (A [ σ ]T)) → Sub Γ (Δ ▷[ i ] A)
      ,∘ : {t : Tm Γ i (A [ σ ]T)} → (σ ,, t) ∘ ρ ≡ (σ ∘ ρ) ,, coeTm (sym [∘]T) (t [ ρ ])
      p,q : p {Γ} {i} {A} ,, q ≡ id
      p∘, : {t : Tm Γ i (A [ σ ]T)} → p ∘ (σ ,, t) ≡ σ
      q[,] : q [ σ ,, t ] ≡[ cong (Tm Γ i) (trans (sym [∘]T) (cong (A [_]T) p∘,)) ] t

      -- Context extension for #
      _▷# : (Γ : Con) → Con
      p# : Sub (Γ ▷#) Γ
      q# : #∈ (Γ ▷#)
      _,#_ : (σ : Sub Γ Δ) → (π : #∈ Γ) → Sub Γ (Δ ▷#)
      ,#∘ : (σ ,# π) ∘ ρ ≡ (σ ∘ ρ) ,# (π [ ρ ]#)
      p,#q : p# {Γ} ,# q# ≡ id
      p∘,# : p# ∘ (σ ,# π) ≡ σ
      q[,#] : q# [ σ ,# π ]# ≡ π

    ⟨_⟩ : (t : Tm Γ i A) → Sub Γ (Γ ▷[ i ] A)
    ⟨ t ⟩ = id ,, (t [ id ])

    _⁺ : (σ : Sub Γ Δ) → Sub (Γ ▷[ i ] (A [ σ ]T)) (Δ ▷[ i ] A)
    σ ⁺ = (σ ∘ p) ,, coeTm (sym [∘]T) q

    _⁺# : (σ : Sub Γ Δ) → Sub (Γ ▷#) (Δ ▷#)
    σ ⁺# = (σ ∘ p#) ,# q#
        
    field
      -- Conversion between terms
      ↓ : Tm (Γ ▷#) ω (A [ p# ]T) → Tm Γ z A
      ↑ : Tm Γ z A → Tm (Γ ▷#) ω (A [ p# ]T)

      -- This type is ugly
      ↓[] : (↓ t) [ σ ] ≡ ↓
        (coeTm (trans (sym [∘]T) (trans (cong (A [_]T) p∘,#) [∘]T))
        (t [ σ ⁺# ]))  

      -- Luckily the other direction is derivable (and I will not derive it)

      ↑↓ : ↑ (↓ t) ≡ t
      ↓↑ : ↓ (↑ t) ≡ t
  
    pz' : Sub (Γ ▷[ ω ] A) (Γ ▷[ z ] A)
    pz' = p ,, ↓ (q [ p# ])

    field
      -- TODO: prove this
      pz∘⁺≡⁺∘pz' : (_⁺ {Γ} {A = A} σ) ∘ pz' {Γ} ≡ pz' ∘ (σ ⁺)

    ↓* : Tm Γ i A → Tm Γ z A
    ↓* {i = z} t = t
    ↓* {i = ω} t = ↓ (t [ p# ])
  
    pz : Sub (Γ ▷[ i ] A) (Γ ▷[ z ] A)
    pz = p ,, ↓* q

    pz∘⁺≡⁺∘pz : (_⁺ {Γ} {A = A} σ) ∘ pz {Γ} {ω} ≡ pz ∘ (σ ⁺)
    pz∘⁺≡⁺∘pz {Γ = Γ} {A = A} {σ = σ} = pz∘⁺≡⁺∘pz'

    [pz][⁺]≡[⁺][pz] : (A [ σ ⁺ ]T) [ pz {Γ} {i} ]T ≡ (A [ pz ]T) [ σ ⁺ ]T
    [pz][⁺]≡[⁺][pz] {A = A} {Γ = Γ} {σ = σ} {i = z} =
       trans (cong ((A [ σ ⁺ ]T) [_]T) p,q)
       (trans [id]T ((cong (λ A → A [ σ ⁺ ]T) (sym (trans (cong (_ [_]T) p,q) [id]T)))))
    [pz][⁺]≡[⁺][pz] {A = A} {Γ = Γ} {σ = σ} {i = ω} =
      trans (sym [∘]T) (trans (cong (A [_]T) pz∘⁺≡⁺∘pz) [∘]T)

  module in-CwFwE-core (c : CwFwE-core) where
    open CwFwE-core c

    record Π-structure  : Set where
      field
        Π : (i : Mode) → (A : Ty Γ) → (B : Ty (Γ ▷[ z ] A)) → Ty Γ
        Π[] : (Π i A B) [ σ ]T ≡ Π i (A [ σ ]T) (B [ σ ⁺ ]T)

        lam : (f : Tm (Γ ▷[ i ] A) ω (B [ pz ]T)) → Tm Γ ω (Π i A B)
        lam[] : (lam {i = i} t) [ σ ]
          ≡[ cong (Tm _ _) Π[] ] lam (coeTm (sym [pz][⁺]≡[⁺][pz]) (t [ σ ⁺ ]))

        ap : (f : Tm Γ ω (Π i A B)) → Tm (Γ ▷[ i ] A) ω (B [ pz ]T)

        Πβ : ap {i = i} (lam t) ≡ t
        Πη : lam {i = i} (ap t) ≡ t

    record U-structure : Set where
      field
        U : Ty Γ
        U[] : U [ σ ]T ≡ U

        El : (t : Tm Γ z U) → Ty Γ
        El[] : (El t) [ σ ]T ≡ El (subst (Tm _ _) U[] (t [ σ ]))

        code : (A : Ty Γ) → Tm Γ z U
        code[] : (code A) [ σ ] ≡[ cong (Tm _ _) U[] ] code (A [ σ ]T)

        El-code : El (code A) ≡ A
        code-El : code (El t) ≡ t


    -- Full Π, doesn't work
    record Π'-structure  : Set where
      field
        Π' : (A : Ty Γ) → (B : Ty (Γ ▷[ ω ] A)) → Ty Γ
        Π'[] : (Π' A B) [ σ ]T ≡ Π' (A [ σ ]T) (B [ σ ⁺ ]T)

        lam' : (f : Tm (Γ ▷[ ω ] A) ω B) → Tm Γ ω (Π' A B)
        lam'[] : (lam' t) [ σ ] ≡[ cong (Tm _ _) Π'[] ] lam' (t [ σ ⁺ ])

        ap' : (f : Tm Γ ω (Π' A B)) → Tm (Γ ▷[ ω ] A) ω B

        Πβ' : ap' (lam' t) ≡ t
        Πη' : lam' (ap' t) ≡ t
