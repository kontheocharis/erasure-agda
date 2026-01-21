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
    Γ Γ' Δ Δ' Θ : Con
    σ τ ρ : Sub Γ Δ
    A A' B C : Ty Γ
    t u v : Tm Γ i A
    π ξ : #∈ Γ

  opaque
    unfolding coe

    ap-Subᶜ : Γ ≡ Γ' → Δ ≡ Δ' → Sub Γ Δ ≡ Sub Γ' Δ'
    ap-Subᶜ refl refl = refl

    ap-Tyᶜ : Γ ≡ Γ' → Ty Γ ≡ Ty Γ'
    ap-Tyᶜ refl = refl

    ap-#∈ᶜ : Γ ≡ Γ' → #∈ Γ ≡ #∈ Γ'
    ap-#∈ᶜ refl = refl

    ap-Tm : A ≡ A' → Tm Γ i A ≡ Tm Γ i A'
    ap-Tm refl = refl

    ap-Tmᶜ : (e : Γ ≡ Γ') → A ≡[ ap-Tyᶜ e ] A' → Tm Γ i A ≡ Tm Γ' i A'
    ap-Tmᶜ refl refl = refl


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

    opaque
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

record CwFwE : Set where
  field
    sorts : CwFwE-sorts
  open in-CwFwE-sorts sorts
  field
    core : CwFwE-core
  open in-CwFwE-core core
  field
    Π-str : Π-structure
    U-str : U-structure

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
    Γᴰ Γᴰ' Δᴰ Δᴰ' Θᴰ : Conᴰ Γ
    σᴰ τᴰ ρᴰ : Subᴰ Γᴰ Δᴰ σ
    Aᴰ Aᴰ' Bᴰ Cᴰ : Tyᴰ Γᴰ A
    tᴰ uᴰ vᴰ : Tmᴰ Γᴰ i Aᴰ t
    πᴰ : #∈ᴰ Γᴰ π

  opaque
    unfolding coe

    ap-Conᴰᶜ : Γ ≡ Δ → Conᴰ Γ ≡ Conᴰ Δ
    ap-Conᴰᶜ refl = refl

    ap-Subᴰ : σ ≡ τ → Subᴰ Γᴰ Δᴰ σ ≡ Subᴰ Γᴰ Δᴰ τ
    ap-Subᴰ refl = refl

    ap-Subᴰᶜ : (pΓ : Γ ≡ Γ') → (pΔ : Δ ≡ Δ')
      → Γᴰ ≡[ ap-Conᴰᶜ pΓ ] Γᴰ'
      → Δᴰ ≡[ ap-Conᴰᶜ pΔ ] Δᴰ'
      → σ ≡[ ap-Subᶜ pΓ pΔ ] τ
      → Subᴰ Γᴰ Δᴰ σ ≡ Subᴰ Γᴰ' Δᴰ' τ
    ap-Subᴰᶜ refl refl refl refl refl = refl

    ap-Tyᴰ : A ≡ B → Tyᴰ Γᴰ A ≡ Tyᴰ Γᴰ B
    ap-Tyᴰ refl = refl

    ap-Tyᴰᶜ : (pΓ : Γ ≡ Δ)
      → Γᴰ ≡[ ap-Conᴰᶜ pΓ ] Δᴰ
      → A ≡[ ap-Tyᶜ pΓ ] B
      → Tyᴰ Γᴰ A ≡ Tyᴰ Δᴰ B
    ap-Tyᴰᶜ refl refl refl = refl

    ap-#∈ᴰ : π ≡ ξ → #∈ᴰ Γᴰ π ≡ #∈ᴰ Γᴰ ξ
    ap-#∈ᴰ refl = refl

    ap-#∈ᴰᶜ : (pΓ : Γ ≡ Δ)
      → Γᴰ ≡[ ap-Conᴰᶜ pΓ ] Δᴰ
      → π ≡[ ap-#∈ᶜ pΓ ] ξ
      → #∈ᴰ Γᴰ π ≡ #∈ᴰ Δᴰ ξ
    ap-#∈ᴰᶜ refl refl refl = refl

    ap-Tmᴰ : (p : A ≡ B)
      → Aᴰ ≡[ ap-Tyᴰ p ] Bᴰ
      → t ≡[ ap-Tm p ] u
      → Tmᴰ Γᴰ i Aᴰ t ≡ Tmᴰ Γᴰ i Bᴰ u
    ap-Tmᴰ refl refl refl = refl

    ap-Tmᴰᶜ : (pΓ : Γ ≡ Δ) → (pA : A ≡[ ap-Tyᶜ pΓ ] B)
      → (pΓᴰ : Γᴰ ≡[ ap-Conᴰᶜ pΓ ] Δᴰ)
      → Aᴰ ≡[ ap-Tyᴰᶜ pΓ pΓᴰ pA ] Bᴰ
      → t ≡[ ap-Tmᶜ pΓ pA ] u
      → Tmᴰ Γᴰ i Aᴰ t ≡ Tmᴰ Δᴰ i Bᴰ u
    ap-Tmᴰᶜ refl refl refl refl refl = refl

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

    opaque
      unfolding ↓*

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

record CwFwEᴰ (base : CwFwE) : Set where
  open CwFwE base
  field
    sortsᴰ : CwFwEᴰ-sorts sorts
  open in-CwFwEᴰ-sorts sortsᴰ core
  field
    coreᴰ : CwFwEᴰ-core
  open in-CwFwEᴰ-core coreᴰ
  field
    Π-strᴰ : Π-structureᴰ Π-str
    U-strᴰ : U-structureᴰ U-str


-- Syntax

module CwFwE-syntax where
  postulate
    syn : CwFwE

  open CwFwE syn
  open CwFwE-sorts sorts public
  open in-CwFwE-sorts sorts public
  open in-CwFwE-sorts.CwFwE-core core public
  open in-CwFwE-sorts.in-CwFwE-core sorts core public

  -- Injectivity for syntax sorts
  postulate
    Sub-inj₀ : Sub Γ Δ ≡ Sub Γ' Δ' → Γ ≡ Γ'
    Sub-inj₁ : Sub Γ Δ ≡ Sub Γ' Δ' → Δ ≡ Δ'

    Ty-inj : Ty Γ ≡ Ty Γ' → Γ ≡ Γ'

    #∈-inj : #∈ Γ ≡ #∈ Γ' → Γ ≡ Γ'

    Tm-injᶜ : Tm Γ i A ≡ Tm Γ' i A' → Γ ≡ Γ'
    Tm-injᵀ : (e : Tm Γ i A ≡ Tm Γ' i A') → A ≡[ ap-Tyᶜ (Tm-injᶜ e) ] A'

  -- Eliminator
  module CwFwE-elim (methods : CwFwEᴰ syn) where
    open CwFwEᴰ methods
    open CwFwEᴰ-sorts sortsᴰ
    open in-CwFwEᴰ-sorts sortsᴰ core
    open in-CwFwEᴰ-sorts.CwFwEᴰ-core coreᴰ
    open in-CwFwEᴰ-sorts.in-CwFwEᴰ-core sortsᴰ core coreᴰ

    postulate
       ⟦_⟧ᶜ : (Γ : Con) → Conᴰ Γ
       ⟦_⟧ˢ : (σ : Sub Γ Δ) → Subᴰ ⟦ Γ ⟧ᶜ ⟦ Δ ⟧ᶜ σ
       ⟦_⟧ᵀ : (A : Ty Γ) → Tyᴰ ⟦ Γ ⟧ᶜ A
       ⟦_⟧̂# : (π : #∈ Γ) → #∈ᴰ ⟦ Γ ⟧ᶜ π
       ⟦_⟧ᵗ : (a : Tm Γ i A) → Tmᴰ ⟦ Γ ⟧ᶜ i ⟦ A ⟧ᵀ a

    opaque
      unfolding coe

      ap-⟦⟧ᶜ : (e : Γ ≡ Γ') → ⟦ Γ ⟧ᶜ ≡[ ap-Conᴰᶜ e ] ⟦ Γ' ⟧ᶜ
      ap-⟦⟧ᶜ refl = refl

      ap-⟦⟧ᵀ : (eΓ : Γ ≡ Γ') → (eA : A ≡[ ap-Tyᶜ eΓ ] A')
        → ⟦ A ⟧ᵀ ≡[ ap-Tyᴰᶜ eΓ (ap-⟦⟧ᶜ eΓ) eA ] ⟦ A' ⟧ᵀ
      ap-⟦⟧ᵀ refl refl = refl

    postulate
       ⟦coe⟧ˢ : ∀ (p : Sub Γ Δ ≡ Sub Γ' Δ') →
        ⟦ coe p σ ⟧ˢ
          ≡ coe (ap-Subᴰᶜ (Sub-inj₀ p) (Sub-inj₁ p) (ap-⟦⟧ᶜ (Sub-inj₀ p)) (ap-⟦⟧ᶜ (Sub-inj₁ p)) refl ) ⟦ σ ⟧ˢ
       {-# REWRITE ⟦coe⟧ˢ #-}

       ⟦coe⟧ᵀ : ∀ (p : Ty Γ ≡ Ty Γ') →
        ⟦ coe p A ⟧ᵀ
          ≡ coe (ap-Tyᴰᶜ (Ty-inj p) (ap-⟦⟧ᶜ (Ty-inj p)) refl) ⟦ A ⟧ᵀ
       {-# REWRITE ⟦coe⟧ᵀ #-}

       ⟦coe⟧̂# : ∀ (p : #∈ Γ ≡ #∈ Γ') →
        ⟦ coe p π ⟧̂#
          ≡ coe (ap-#∈ᴰᶜ (#∈-inj p) (ap-⟦⟧ᶜ (#∈-inj p)) refl) ⟦ π ⟧̂#
       {-# REWRITE ⟦coe⟧̂# #-}

       ⟦coe⟧ᵗ : ∀ (p : Tm Γ i A ≡ Tm Γ' i A') →
        ⟦ coe p t ⟧ᵗ
          ≡ coe (ap-Tmᴰᶜ (Tm-injᶜ p) (Tm-injᵀ p) (ap-⟦⟧ᶜ (Tm-injᶜ p)) (ap-⟦⟧ᵀ (Tm-injᶜ p) (Tm-injᵀ p)) refl) ⟦ t ⟧ᵗ
       {-# REWRITE ⟦coe⟧ᵗ #-}

    postulate
       ⟦∙⟧ : ⟦ ∙ ⟧ᶜ ≡ ∙ᴰ
       {-# REWRITE ⟦∙⟧ #-}

       ⟦id⟧ : ⟦ id {Γ} ⟧ˢ ≡ idᴰ
       {-# REWRITE ⟦id⟧ #-}

       ⟦∘⟧ : ⟦ σ ∘ τ ⟧ˢ ≡ ⟦ σ ⟧ˢ ∘ᴰ ⟦ τ ⟧ˢ
       {-# REWRITE ⟦∘⟧ #-}

       ⟦ε⟧ : ⟦ ε {Γ} ⟧ˢ ≡ εᴰ
       {-# REWRITE ⟦ε⟧ #-}

       ⟦▷⟧ : ⟦ Γ ▷[ i ] A ⟧ᶜ ≡ ⟦ Γ ⟧ᶜ ▷ᴰ[ i ] ⟦ A ⟧ᵀ
       {-# REWRITE ⟦▷⟧ #-}

       ⟦▷#⟧ : ⟦ Γ ▷# ⟧ᶜ ≡ ⟦ Γ ⟧ᶜ ▷#ᴰ
       {-# REWRITE ⟦▷#⟧ #-}

       ⟦[]T⟧ : ⟦ A [ σ ]T ⟧ᵀ ≡ ⟦ A ⟧ᵀ [ ⟦ σ ⟧ˢ ]Tᴰ
       {-# REWRITE ⟦[]T⟧ #-}

       ⟦p⟧ : ⟦ p {Γ} {i} {A} ⟧ˢ ≡ pᴰ
       {-# REWRITE ⟦p⟧ #-}

       ⟦p#⟧ : ⟦ p# {Γ} ⟧ˢ ≡ p#ᴰ
       {-# REWRITE ⟦p#⟧ #-}
       
       ⟦[]⟧ : ⟦ t [ σ ] ⟧ᵗ ≡ (⟦ t ⟧ᵗ [ ⟦ σ ⟧ˢ ]ᴰ)
       {-# REWRITE ⟦[]⟧ #-}

       ⟦[]#⟧ : ⟦ π [ σ ]# ⟧̂# ≡ ⟦ π ⟧̂# [ ⟦ σ ⟧ˢ ]#ᴰ
       {-# REWRITE ⟦[]#⟧ #-}

       ⟦q⟧ : ⟦ q {Γ} {i} {A} ⟧ᵗ ≡ qᴰ
       {-# REWRITE ⟦q⟧ #-}

       ⟦,,⟧ : ⟦ σ ,, t ⟧ˢ ≡ ⟦ σ ⟧ˢ ,,ᴰ ⟦ t ⟧ᵗ
       {-# REWRITE ⟦,,⟧ #-}

       ⟦q#⟧ : ⟦ q# {Γ} ⟧̂# ≡ q#ᴰ
       {-# REWRITE ⟦q#⟧ #-}

       ⟦,#⟧ : ⟦ σ ,# π ⟧ˢ ≡ ⟦ σ ⟧ˢ ,#ᴰ ⟦ π ⟧̂#
       {-# REWRITE ⟦,#⟧ #-}

       ⟦↓⟧ : ⟦ ↓ t ⟧ᵗ ≡ ↓ᴰ ⟦ t ⟧ᵗ
       {-# REWRITE ⟦↓⟧ #-}

       ⟦↑⟧ : ⟦ ↑ t ⟧ᵗ ≡ ↑ᴰ ⟦ t ⟧ᵗ
       {-# REWRITE ⟦↑⟧ #-}

    opaque
      unfolding ↓*ᴰ

      ⟦↓*⟧ : {t : Tm Γ i A} → ⟦ ↓* t ⟧ᵗ ≡ ↓*ᴰ ⟦ t ⟧ᵗ
      ⟦↓*⟧ {i = z} = refl
      ⟦↓*⟧ {i = ω} = refl

    {-# REWRITE ⟦↓*⟧ #-}

    opaque
      unfolding pzᴰ

      ⟦pz⟧ : ⟦ pz {Γ} {i} {A} ⟧ˢ ≡ pzᴰ
      ⟦pz⟧ {i = z} = refl
      ⟦pz⟧ {i = ω} = refl

    {-# REWRITE ⟦pz⟧ #-}

    open Π-structure Π-str
    open Π-structureᴰ Π-strᴰ
    open U-structure U-str
    open U-structureᴰ U-strᴰ

    postulate
       ⟦Π⟧ : ⟦ Π i A B ⟧ᵀ ≡ Πᴰ i ⟦ A ⟧ᵀ ⟦ B ⟧ᵀ
       {-# REWRITE ⟦Π⟧ #-}

       ⟦lam⟧ : ⟦ lam {i = i} t ⟧ᵗ ≡ lamᴰ ⟦ t ⟧ᵗ
       {-# REWRITE ⟦lam⟧ #-}

       ⟦ap⟧ : ⟦ ap {i = i} t ⟧ᵗ ≡ apᴰ ⟦ t ⟧ᵗ
       {-# REWRITE ⟦ap⟧ #-}

       ⟦U⟧ : ⟦ U {Γ} ⟧ᵀ ≡ Uᴰ
       {-# REWRITE ⟦U⟧ #-}

       ⟦El⟧ : ⟦ El t ⟧ᵀ ≡ Elᴰ ⟦ t ⟧ᵗ
       {-# REWRITE ⟦El⟧ #-}

       ⟦code⟧ : ⟦ code A ⟧ᵗ ≡ codeᴰ ⟦ A ⟧ᵀ
       {-# REWRITE ⟦code⟧ #-}
