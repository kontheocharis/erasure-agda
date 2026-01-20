{-# OPTIONS --type-in-type #-}
module Theories.CwFwE where

open import Agda.Primitive
open import Utils
open import Mode

-- Model

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
    σ τ ρ : Sub Γ Δ
    A B C : Ty Γ
    t u v : Tm Γ i A
    π ξ : #∈ Γ

  opaque
    ap-Tm : A ≡ B → Tm Γ i A ≡ Tm Γ i B
    ap-Tm refl = refl

  module core-utils (_[_]T : ∀ {Γ Δ} → (A : Ty Δ) → (σ : Sub Γ Δ) → Ty Γ) where
    opaque
      ap-[]T₀-impl : σ ≡ τ → A [ σ ]T ≡ A [ τ ]T
      ap-[]T₀-impl refl = refl
      
      ap-[]T₁-impl : A ≡ B → A [ σ ]T ≡ B [ σ ]T
      ap-[]T₁-impl refl = refl

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
      [id] : (t [ id ]) ≡[ ap-Tm [id]T ] t
      [id]# : π [ id ]# ≡ π
      [∘]T : A [ σ ∘ τ ]T ≡ (A [ σ ]T) [ τ ]T
      [∘] : t [ σ ∘ τ ] ≡[ ap-Tm [∘]T ] ((t [ σ ]) [ τ ])
      [∘]# : π [ σ ∘ τ ]# ≡ (π [ σ ]#) [ τ ]#
      
      -- Context extension for terms
      _▷[_]_ : (Γ : Con) → Mode → (A : Ty Γ) → Con

    ap-[]T₀ : σ ≡ τ → A [ σ ]T ≡ A [ τ ]T
    ap-[]T₀ = core-utils.ap-[]T₀-impl _[_]T

    ap-[]T₁ : A ≡ B → A [ σ ]T ≡ B [ σ ]T
    ap-[]T₁ = core-utils.ap-[]T₁-impl _[_]T

    field
      p : Sub (Γ ▷[ i ] A) Γ
      q : Tm (Γ ▷[ i ] A) i (A [ p ]T)
      _,,_ : (σ : Sub Γ Δ) → (t : Tm Γ i (A [ σ ]T)) → Sub Γ (Δ ▷[ i ] A)
      ,∘ : (σ ,, t) ∘ ρ ≡ (σ ∘ ρ) ,, coe (ap-Tm (sym [∘]T)) (t [ ρ ])
      p,q : p {Γ} {i} {A} ,, q ≡ id
      p∘, : p ∘ (σ ,, t) ≡ σ
      q[,] : q [ σ ,, t ] ≡[ ap-Tm (trans (sym [∘]T) (ap-[]T₀ p∘,)) ] t

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
    σ ⁺ = (σ ∘ p) ,, coe (ap-Tm (sym [∘]T)) q

    _⁺# : (σ : Sub Γ Δ) → Sub (Γ ▷#) (Δ ▷#)
    σ ⁺# = (σ ∘ p#) ,# q#
        
    field
      -- Conversion between terms
      ↓ : Tm (Γ ▷#) ω (A [ p# ]T) → Tm Γ z A
      ↑ : Tm Γ z A → Tm (Γ ▷#) ω (A [ p# ]T)

      -- This type is ugly
      ↓[] : (↓ t) [ σ ] ≡ ↓
        (coe (ap-Tm (trans (sym [∘]T) (trans (ap-[]T₀ p∘,#) [∘]T)))
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
       trans (ap-[]T₀ p,q)
       (trans [id]T ((ap-[]T₁ (sym (trans (ap-[]T₀ p,q) [id]T)))))
    [pz][⁺]≡[⁺][pz] {A = A} {Γ = Γ} {σ = σ} {i = ω} =
      trans (sym [∘]T) (trans (ap-[]T₀ pz∘⁺≡⁺∘pz) [∘]T)

  module in-CwFwE-core (c : CwFwE-core) where
    open CwFwE-core c

    record Π-structure  : Set where
      field
        Π : (i : Mode) → (A : Ty Γ) → (B : Ty (Γ ▷[ z ] A)) → Ty Γ
        Π[] : (Π i A B) [ σ ]T ≡ Π i (A [ σ ]T) (B [ σ ⁺ ]T)

        lam : (f : Tm (Γ ▷[ i ] A) ω (B [ pz ]T)) → Tm Γ ω (Π i A B)
        lam[] : (lam {i = i} t) [ σ ]
          ≡[ ap-Tm Π[] ] lam (coe (ap-Tm (sym [pz][⁺]≡[⁺][pz])) (t [ σ ⁺ ]))

        ap : (f : Tm Γ ω (Π i A B)) → Tm (Γ ▷[ i ] A) ω (B [ pz ]T)

        Πβ : ap {i = i} (lam t) ≡ t
        Πη : lam {i = i} (ap t) ≡ t

    record U-structure : Set where
      field
        U : Ty Γ
        U[] : U [ σ ]T ≡ U

        El : (t : Tm Γ z U) → Ty Γ
        El[] : (El t) [ σ ]T ≡ El (coe (ap-Tm U[]) (t [ σ ]))

        code : (A : Ty Γ) → Tm Γ z U
        code[] : (code A) [ σ ] ≡[ ap-Tm U[] ] code (A [ σ ]T)

        El-code : El (code A) ≡ A
        code-El : code (El t) ≡ t

    -- Π whose bound type is relevant
    record Π'-structure  : Set where
      field
        Π' : (A : Ty Γ) → (B : Ty (Γ ▷[ ω ] A)) → Ty Γ
        Π'[] : (Π' A B) [ σ ]T ≡ Π' (A [ σ ]T) (B [ σ ⁺ ]T)

        lam' : (f : Tm (Γ ▷[ ω ] A) ω B) → Tm Γ ω (Π' A B)
        lam'[] : (lam' t) [ σ ] ≡[ ap-Tm Π'[] ] lam' (t [ σ ⁺ ])

        ap' : (f : Tm Γ ω (Π' A B)) → Tm (Γ ▷[ ω ] A) ω B

        Πβ' : ap' (lam' t) ≡ t
        Πη' : lam' (ap' t) ≡ t


record CwFwE : Set where
  field
    sorts : CwFwE-sorts
  open in-CwFwE-sorts
  field
    core : CwFwE-core sorts

-- Displayed model

    
record CwFwEᴰ-sorts (s : CwFwE-sorts) : Set where
  open CwFwE-sorts s
  field
    Conᴰ : Con → Set
    Subᴰ : ∀ {Γ Δ} → Conᴰ Γ → Conᴰ Δ → Sub Γ Δ → Set
    Tyᴰ : ∀ {Γ} → Conᴰ Γ → Ty Γ → Set
    #∈ᴰ : ∀ {Γ} → Conᴰ Γ → #∈ Γ → Set
    Tmᴰ : ∀ {Γ A} → (Γᴰ : Conᴰ Γ) → (i : Mode) → Tyᴰ Γᴰ A → Tm Γ i A → Set

module in-CwFwEᴰ-sorts {s : CwFwE-sorts} (sᴰ : CwFwEᴰ-sorts s) (c : in-CwFwE-sorts.CwFwE-core s) where
  open CwFwE-sorts s
  open CwFwEᴰ-sorts sᴰ
  open in-CwFwE-sorts s
  open CwFwE-core c
  open in-CwFwE-core c
  variable
    Γᴰ Δᴰ Θᴰ : Conᴰ Γ
    σᴰ τᴰ ρᴰ : Subᴰ Γᴰ Δᴰ σ
    Aᴰ Bᴰ Cᴰ : Tyᴰ Γᴰ A
    tᴰ uᴰ vᴰ : Tmᴰ Γᴰ i Aᴰ t
    πᴰ : #∈ᴰ Γᴰ π

  opaque
    unfolding coe

    ap-Subᴰ : σ ≡ τ → Subᴰ Γᴰ Δᴰ σ ≡ Subᴰ Γᴰ Δᴰ τ
    ap-Subᴰ refl = refl

    ap-Tyᴰ : A ≡ B → Tyᴰ Γᴰ A ≡ Tyᴰ Γᴰ B
    ap-Tyᴰ refl = refl

    ap-#∈ᴰ : π ≡ ξ → #∈ᴰ Γᴰ π ≡ #∈ᴰ Γᴰ ξ
    ap-#∈ᴰ refl = refl

    ap-Tmᴰ : (p : A ≡ B)
      → Aᴰ ≡[ ap-Tyᴰ p ] Bᴰ
      → t ≡[ ap-Tm p ] u
      → Tmᴰ Γᴰ i Aᴰ t ≡ Tmᴰ Γᴰ i Bᴰ u
    ap-Tmᴰ refl refl refl = refl

  module core-utilsᴰ
    (_[_]Tᴰ : ∀ {Γ Δ A σ} {Γᴰ : Conᴰ Γ} {Δᴰ : Conᴰ Δ}
      → Tyᴰ Δᴰ A → Subᴰ Γᴰ Δᴰ σ → Tyᴰ Γᴰ (A [ σ ]T))
    where
    opaque
      unfolding ap-Subᴰ ap-Tyᴰ
      ap-[]T₀ᴰ : (p : σ ≡ τ) → σᴰ ≡[ ap-Subᴰ p ] τᴰ
        → Aᴰ [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ (ap-[]T₀ p) ] (Aᴰ [ τᴰ ]Tᴰ)
      ap-[]T₀ᴰ refl refl = refl

      ap-[]T₁ᴰ : (p : A ≡ B) → Aᴰ ≡[ ap-Tyᴰ p ] Bᴰ
        → Aᴰ [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ (ap-[]T₁ p) ] (Bᴰ [ σᴰ ]Tᴰ)
      ap-[]T₁ᴰ refl refl = refl

  record CwFwEᴰ-core : Set where
    field
      idᴰ : Subᴰ Γᴰ Γᴰ id
      _∘ᴰ_ : Subᴰ Δᴰ Θᴰ σ → Subᴰ Γᴰ Δᴰ τ → Subᴰ Γᴰ Θᴰ (σ ∘ τ)
      assocᴰ : ρᴰ ∘ᴰ (σᴰ ∘ᴰ τᴰ) ≡[ ap-Subᴰ assoc ] (ρᴰ ∘ᴰ σᴰ) ∘ᴰ τᴰ
      ∘idᴰ : idᴰ ∘ᴰ σᴰ ≡[ ap-Subᴰ ∘id ] σᴰ
      id∘ᴰ : σᴰ ∘ᴰ idᴰ ≡[ ap-Subᴰ id∘ ] σᴰ

      ∙ᴰ : Conᴰ ∙
      εᴰ : Subᴰ Γᴰ ∙ᴰ ε
      ∃!εᴰ : εᴰ {Γᴰ = Γᴰ} ≡[ ap-Subᴰ ∃!ε ] σᴰ

      _[_]Tᴰ : Tyᴰ Δᴰ A → Subᴰ Γᴰ Δᴰ σ → Tyᴰ Γᴰ (A [ σ ]T)
      _[_]ᴰ : Tmᴰ Δᴰ i Aᴰ t → (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Tmᴰ Γᴰ i (Aᴰ [ σᴰ ]Tᴰ) (t [ σ ])
      _[_]#ᴰ : #∈ᴰ Δᴰ π → Subᴰ Γᴰ Δᴰ σ → #∈ᴰ Γᴰ (π [ σ ]#)
      [id]Tᴰ : Aᴰ [ idᴰ ]Tᴰ ≡[ ap-Tyᴰ [id]T ] Aᴰ
      [id]ᴰ : (tᴰ [ idᴰ ]ᴰ) ≡[ ap-Tmᴰ [id]T [id]Tᴰ [id] ] tᴰ
      [id]#ᴰ : πᴰ [ idᴰ ]#ᴰ ≡[ ap-#∈ᴰ [id]# ] πᴰ
      [∘]Tᴰ : Aᴰ [ σᴰ ∘ᴰ τᴰ ]Tᴰ ≡[ ap-Tyᴰ [∘]T ] (Aᴰ [ σᴰ ]Tᴰ) [ τᴰ ]Tᴰ
      [∘]ᴰ : (tᴰ [ σᴰ ∘ᴰ τᴰ ]ᴰ) ≡[ ap-Tmᴰ [∘]T [∘]Tᴰ [∘] ] ((tᴰ [ σᴰ ]ᴰ) [ τᴰ ]ᴰ)
      [∘]#ᴰ : πᴰ [ σᴰ ∘ᴰ τᴰ ]#ᴰ ≡[ ap-#∈ᴰ [∘]# ] (πᴰ [ σᴰ ]#ᴰ) [ τᴰ ]#ᴰ

    ap-[]T₀ᴰ : (p : σ ≡ τ) → σᴰ ≡[ ap-Subᴰ p ] τᴰ
      → Aᴰ [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ (ap-[]T₀ p) ] Aᴰ [ τᴰ ]Tᴰ
    ap-[]T₀ᴰ = core-utilsᴰ.ap-[]T₀ᴰ _[_]Tᴰ

    ap-[]T₁ᴰ : (p : A ≡ B) → Aᴰ ≡[ ap-Tyᴰ p ] Bᴰ
      → Aᴰ [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ (ap-[]T₁ p) ] Bᴰ [ σᴰ ]Tᴰ
    ap-[]T₁ᴰ = core-utilsᴰ.ap-[]T₁ᴰ _[_]Tᴰ

    field
      _▷ᴰ[_]_ : (Γᴰ : Conᴰ Γ) → (i : Mode) → Tyᴰ Γᴰ A → Conᴰ (Γ ▷[ i ] A)
      pᴰ : Subᴰ (Γᴰ ▷ᴰ[ i ] Aᴰ) Γᴰ p
      qᴰ : Tmᴰ (Γᴰ ▷ᴰ[ i ] Aᴰ) i (Aᴰ [ pᴰ ]Tᴰ) q
      _,,ᴰ_ : (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Tmᴰ Γᴰ i (Aᴰ [ σᴰ ]Tᴰ) t → Subᴰ Γᴰ (Δᴰ ▷ᴰ[ i ] Aᴰ) (σ ,, t)
      ,∘ᴰ : (σᴰ ,,ᴰ tᴰ) ∘ᴰ ρᴰ ≡[ ap-Subᴰ ,∘ ]
          (σᴰ ∘ᴰ ρᴰ) ,,ᴰ coe (ap-Tmᴰ (sym [∘]T) (symᴰ [∘]Tᴰ) refl) (tᴰ [ ρᴰ ]ᴰ)
      p,qᴰ : pᴰ {Γᴰ = Γᴰ} {i = i} {Aᴰ = Aᴰ} ,,ᴰ qᴰ ≡[ ap-Subᴰ p,q ] idᴰ
      p∘,ᴰ : pᴰ ∘ᴰ (σᴰ ,,ᴰ tᴰ) ≡[ ap-Subᴰ p∘, ] σᴰ
      q[,]ᴰ : qᴰ [ σᴰ ,,ᴰ tᴰ ]ᴰ
          ≡[ ap-Tmᴰ (trans (sym [∘]T) (ap-[]T₀ p∘,))
                    (transᴰ {p = ap-Tyᴰ (sym [∘]T)} (symᴰ [∘]Tᴰ) (ap-[]T₀ᴰ p∘, p∘,ᴰ))
                    q[,] ]
          tᴰ

      _▷#ᴰ : Conᴰ Γ → Conᴰ (Γ ▷#)
      p#ᴰ : Subᴰ (Γᴰ ▷#ᴰ) Γᴰ p#
      q#ᴰ : #∈ᴰ (Γᴰ ▷#ᴰ) q#
      _,#ᴰ_ : Subᴰ Γᴰ Δᴰ σ → #∈ᴰ Γᴰ π → Subᴰ Γᴰ (Δᴰ ▷#ᴰ) (σ ,# π)
      ,#∘ᴰ : (σᴰ ,#ᴰ πᴰ) ∘ᴰ ρᴰ ≡[ ap-Subᴰ ,#∘ ] (σᴰ ∘ᴰ ρᴰ) ,#ᴰ (πᴰ [ ρᴰ ]#ᴰ)
      p,#qᴰ : p#ᴰ {Γᴰ = Γᴰ} ,#ᴰ q#ᴰ ≡[ ap-Subᴰ p,#q ] idᴰ
      p∘,#ᴰ : p#ᴰ ∘ᴰ (σᴰ ,#ᴰ πᴰ) ≡[ ap-Subᴰ p∘,# ] σᴰ
      q[,#]ᴰ : q#ᴰ [ σᴰ ,#ᴰ πᴰ ]#ᴰ ≡[ ap-#∈ᴰ q[,#] ] πᴰ

    ⟨_⟩ᴰ : (tᴰ : Tmᴰ Γᴰ i Aᴰ t) → Subᴰ Γᴰ (Γᴰ ▷ᴰ[ i ] Aᴰ) ⟨ t ⟩
    ⟨ tᴰ ⟩ᴰ = idᴰ ,,ᴰ (tᴰ [ idᴰ ]ᴰ)

    _⁺ᴰ : (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Subᴰ (Γᴰ ▷ᴰ[ i ] (Aᴰ [ σᴰ ]Tᴰ)) (Δᴰ ▷ᴰ[ i ] Aᴰ) (σ ⁺)
    σᴰ ⁺ᴰ = (σᴰ ∘ᴰ pᴰ) ,,ᴰ coe (ap-Tmᴰ (sym [∘]T) (symᴰ [∘]Tᴰ) refl) qᴰ

    _⁺#ᴰ : (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Subᴰ (Γᴰ ▷#ᴰ) (Δᴰ ▷#ᴰ) (σ ⁺#)
    σᴰ ⁺#ᴰ = (σᴰ ∘ᴰ p#ᴰ) ,#ᴰ q#ᴰ

    field
      ↓ᴰ : Tmᴰ (Γᴰ ▷#ᴰ) ω (Aᴰ [ p#ᴰ ]Tᴰ) t → Tmᴰ Γᴰ z Aᴰ (↓ t)
      ↑ᴰ : Tmᴰ Γᴰ z Aᴰ t → Tmᴰ (Γᴰ ▷#ᴰ) ω (Aᴰ [ p#ᴰ ]Tᴰ) (↑ t)
      ↓[]ᴰ : (↓ᴰ tᴰ) [ σᴰ ]ᴰ ≡[ ap-Tmᴰ refl reflᴰ (dep ↓[]) ]
        ↓ᴰ (coe (ap-Tmᴰ (trans (sym [∘]T) (trans (ap-[]T₀ p∘,#) [∘]T))
                   (transᴰ {p = ap-Tyᴰ (sym [∘]T)} (symᴰ [∘]Tᴰ)
                   (transᴰ {p = ap-Tyᴰ (ap-[]T₀ p∘,#)} (ap-[]T₀ᴰ p∘,# p∘,#ᴰ) [∘]Tᴰ)) refl)
                   (tᴰ [ σᴰ ⁺#ᴰ ]ᴰ))
      ↑↓ᴰ : ↑ᴰ (↓ᴰ tᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep ↑↓) ] tᴰ
      ↓↑ᴰ : ↓ᴰ (↑ᴰ tᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep ↓↑) ] tᴰ

    pz'ᴰ : Subᴰ (Γᴰ ▷ᴰ[ ω ] Aᴰ) (Γᴰ ▷ᴰ[ z ] Aᴰ) pz'
    pz'ᴰ = pᴰ ,,ᴰ ↓ᴰ (qᴰ [ p#ᴰ ]ᴰ)

    field
      pz∘⁺≡⁺∘pz'ᴰ : (_⁺ᴰ {Γᴰ = Γᴰ} {Aᴰ = Aᴰ} σᴰ) ∘ᴰ pz'ᴰ {Γᴰ = Γᴰ}
        ≡[ ap-Subᴰ pz∘⁺≡⁺∘pz' ]
        pz'ᴰ ∘ᴰ (σᴰ ⁺ᴰ)

    ↓*ᴰ : Tmᴰ Γᴰ i Aᴰ t → Tmᴰ Γᴰ z Aᴰ (↓* t)
    ↓*ᴰ {i = z} tᴰ = tᴰ
    ↓*ᴰ {i = ω} tᴰ = ↓ᴰ (tᴰ [ p#ᴰ ]ᴰ)

    pzᴰ : Subᴰ (Γᴰ ▷ᴰ[ i ] Aᴰ) (Γᴰ ▷ᴰ[ z ] Aᴰ) pz
    pzᴰ = pᴰ ,,ᴰ ↓*ᴰ qᴰ

    pz∘⁺≡⁺∘pzᴰ : (_⁺ᴰ {Γᴰ = Γᴰ} {Aᴰ = Aᴰ} σᴰ) ∘ᴰ pzᴰ {Γᴰ = Γᴰ} {i = ω}
      ≡[ ap-Subᴰ pz∘⁺≡⁺∘pz ]
      pzᴰ ∘ᴰ (σᴰ ⁺ᴰ)
    pz∘⁺≡⁺∘pzᴰ {Γᴰ = Γᴰ} {Aᴰ = Aᴰ} {σᴰ = σᴰ} = pz∘⁺≡⁺∘pz'ᴰ

    [pz][⁺]≡[⁺][pz]ᴰ : (Aᴰ [ σᴰ ⁺ᴰ ]Tᴰ) [ pzᴰ {Γᴰ = Γᴰ} {i = i} ]Tᴰ
      ≡[ ap-Tyᴰ [pz][⁺]≡[⁺][pz] ]
      (Aᴰ [ pzᴰ ]Tᴰ) [ σᴰ ⁺ᴰ ]Tᴰ
    [pz][⁺]≡[⁺][pz]ᴰ {Aᴰ = Aᴰ} {Γᴰ = Γᴰ} {σᴰ = σᴰ} {i = z} =
      transᴰ {p = ap-Tyᴰ (ap-[]T₀ p,q)} (ap-[]T₀ᴰ p,q p,qᴰ)
      (transᴰ {p = ap-Tyᴰ [id]T} [id]Tᴰ
      (ap-[]T₁ᴰ (sym (trans (ap-[]T₀ p,q) [id]T))
                (symᴰ (transᴰ {p = ap-Tyᴰ (ap-[]T₀ p,q)} (ap-[]T₀ᴰ p,q p,qᴰ) [id]Tᴰ))))
    [pz][⁺]≡[⁺][pz]ᴰ {Aᴰ = Aᴰ} {Γᴰ = Γᴰ} {σᴰ = σᴰ} {i = ω} =
      transᴰ {p = ap-Tyᴰ (sym [∘]T)} (symᴰ [∘]Tᴰ)
      (transᴰ {p = ap-Tyᴰ (ap-[]T₀ pz∘⁺≡⁺∘pz)} (ap-[]T₀ᴰ pz∘⁺≡⁺∘pz pz∘⁺≡⁺∘pzᴰ) [∘]Tᴰ)

  module in-CwFwEᴰ-core (cᴰ : CwFwEᴰ-core) where
    open CwFwEᴰ-core cᴰ

    record Π-structureᴰ (ps : Π-structure) : Set where
      open Π-structure ps
      field
        Πᴰ : (i : Mode) → (Aᴰ : Tyᴰ Γᴰ A) → (Bᴰ : Tyᴰ (Γᴰ ▷ᴰ[ z ] Aᴰ) B) → Tyᴰ Γᴰ (Π i A B)
        Π[]ᴰ : (Πᴰ i Aᴰ Bᴰ) [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ Π[] ] Πᴰ i (Aᴰ [ σᴰ ]Tᴰ) (Bᴰ [ σᴰ ⁺ᴰ ]Tᴰ)

        lamᴰ : (tᴰ : Tmᴰ (Γᴰ ▷ᴰ[ i ] Aᴰ) ω (Bᴰ [ pzᴰ ]Tᴰ) t) → Tmᴰ Γᴰ ω (Πᴰ i Aᴰ Bᴰ) (lam t)
        lam[]ᴰ : (lamᴰ {i = i} tᴰ) [ σᴰ ]ᴰ
          ≡[ ap-Tmᴰ Π[] Π[]ᴰ lam[] ]
          lamᴰ (coe (ap-Tmᴰ (sym [pz][⁺]≡[⁺][pz]) (symᴰ [pz][⁺]≡[⁺][pz]ᴰ) refl) (tᴰ [ σᴰ ⁺ᴰ ]ᴰ))

        apᴰ : (tᴰ : Tmᴰ Γᴰ ω (Πᴰ i Aᴰ Bᴰ) t) → Tmᴰ (Γᴰ ▷ᴰ[ i ] Aᴰ) ω (Bᴰ [ pzᴰ ]Tᴰ) (ap t)

        Πβᴰ : apᴰ {i = i} (lamᴰ tᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep Πβ) ] tᴰ
        Πηᴰ : lamᴰ {i = i} (apᴰ tᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep Πη) ] tᴰ

    record U-structureᴰ (us : U-structure) : Set where
      open U-structure us
      field
        Uᴰ : Tyᴰ Γᴰ U
        U[]ᴰ : Uᴰ [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ U[] ] Uᴰ

        Elᴰ : (tᴰ : Tmᴰ Γᴰ z Uᴰ t) → Tyᴰ Γᴰ (El t)
        El[]ᴰ : (Elᴰ tᴰ) [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ El[] ] Elᴰ (coe (ap-Tmᴰ U[] U[]ᴰ refl) (tᴰ [ σᴰ ]ᴰ))

        codeᴰ : (Aᴰ : Tyᴰ Γᴰ A) → Tmᴰ Γᴰ z Uᴰ (code A)
        code[]ᴰ : (codeᴰ Aᴰ) [ σᴰ ]ᴰ ≡[ ap-Tmᴰ U[] U[]ᴰ code[] ] codeᴰ (Aᴰ [ σᴰ ]Tᴰ)

        El-codeᴰ : Elᴰ (codeᴰ Aᴰ) ≡[ ap-Tyᴰ El-code ] Aᴰ
        code-Elᴰ : codeᴰ (Elᴰ tᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep code-El) ] tᴰ

    -- Π whose bound type is relevant
    record Π'-structureᴰ (ps : Π'-structure) : Set where
      open Π'-structure ps
      field
        Π'ᴰ : (Aᴰ : Tyᴰ Γᴰ A) → (Bᴰ : Tyᴰ (Γᴰ ▷ᴰ[ ω ] Aᴰ) B) → Tyᴰ Γᴰ (Π' A B)
        Π'[]ᴰ : (Π'ᴰ Aᴰ Bᴰ) [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ Π'[] ] Π'ᴰ (Aᴰ [ σᴰ ]Tᴰ) (Bᴰ [ σᴰ ⁺ᴰ ]Tᴰ)

        lam'ᴰ : (tᴰ : Tmᴰ (Γᴰ ▷ᴰ[ ω ] Aᴰ) ω Bᴰ t) → Tmᴰ Γᴰ ω (Π'ᴰ Aᴰ Bᴰ) (lam' t)
        lam'[]ᴰ : (lam'ᴰ tᴰ) [ σᴰ ]ᴰ ≡[ ap-Tmᴰ Π'[] Π'[]ᴰ lam'[] ] lam'ᴰ (tᴰ [ σᴰ ⁺ᴰ ]ᴰ)

        ap'ᴰ : (tᴰ : Tmᴰ Γᴰ ω (Π'ᴰ Aᴰ Bᴰ) t) → Tmᴰ (Γᴰ ▷ᴰ[ ω ] Aᴰ) ω Bᴰ (ap' t)

        Πβ'ᴰ : ap'ᴰ (lam'ᴰ tᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep Πβ') ] tᴰ
        Πη'ᴰ : lam'ᴰ (ap'ᴰ tᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep Πη') ] tᴰ


module CwFwE-syntax where
  postulate
    syn : CwFwE

  open CwFwE syn
  open CwFwE-sorts sorts
  open in-CwFwE-sorts.CwFwE-core core

  
