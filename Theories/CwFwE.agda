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

  opaque
    ap-Tm : A ≡ B → Tm Γ i A ≡ Tm Γ i B
    ap-Tm refl = refl

  private module core-utils (_[_]T : (A : Ty Δ) → (σ : Sub Γ Δ) → Ty Γ) where
    opaque
      ap-[]T : σ ≡ τ → A [ σ ]T ≡ A [ τ ]T
      ap-[]T refl = refl
      
      ap'-[]T : A ≡ B → A [ σ ]T ≡ B [ σ ]T
      ap'-[]T refl = refl

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

    ap-[]T : σ ≡ τ → A [ σ ]T ≡ A [ τ ]T
    ap-[]T = core-utils.ap-[]T _[_]T

    field
      p : Sub (Γ ▷[ i ] A) Γ
      q : Tm (Γ ▷[ i ] A) i (A [ p ]T)
      _,,_ : (σ : Sub Γ Δ) → (t : Tm Γ i (A [ σ ]T)) → Sub Γ (Δ ▷[ i ] A)
      ,∘ : {t : Tm Γ i (A [ σ ]T)} → (σ ,, t) ∘ ρ ≡ (σ ∘ ρ) ,, coe (ap-Tm (sym [∘]T)) (t [ ρ ])
      p,q : p {Γ} {i} {A} ,, q ≡ id
      p∘, : {t : Tm Γ i (A [ σ ]T)} → p ∘ (σ ,, t) ≡ σ
      q[,] : q [ σ ,, t ] ≡[ ap-Tm (trans (sym [∘]T) (ap-[]T p∘,)) ] t

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
        (coe (ap-Tm (trans (sym [∘]T) (trans (ap-[]T p∘,#) [∘]T)))
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
       (trans [id]T ((cong (λ A → A [ σ ⁺ ]T) (sym (trans (ap-[]T p,q) [id]T)))))
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
    
record CwFwEᴰ-sorts (s : CwFwE-sorts) : Set where
  open CwFwE-sorts s
  field
    Conᴰ : Con → Set
    Subᴰ : ∀ {Γ Δ} → Conᴰ Γ → Conᴰ Δ → Sub Γ Δ → Set
    Tyᴰ : ∀ {Γ} → Conᴰ Γ → Ty Γ → Set
    #∈ᴰ : ∀ {Γ} → Conᴰ Γ → #∈ Γ → Set
    Tmᴰ : ∀ {Γ A} → (Γᴰ : Conᴰ Γ) → (i : Mode) → Tyᴰ Γᴰ A → Tm Γ i A → Set

module in-CwFwEᴰ-sorts {s : CwFwE-sorts} (sᴰ : CwFwEᴰ-sorts s) where
  open CwFwE-sorts s
  open CwFwEᴰ-sorts sᴰ
  open in-CwFwE-sorts s
  variable
    Γᴰ : Conᴰ Γ
    Δᴰ : Conᴰ Δ
    Θᴰ : Conᴰ Θ
    σᴰ : Subᴰ _ _ σ
    τᴰ : Subᴰ _ _ τ
    ρᴰ : Subᴰ _ _ ρ
    Aᴰ : Tyᴰ _ A
    Bᴰ : Tyᴰ _ B
    Cᴰ : Tyᴰ _ C
    tᴰ : Tmᴰ _ _ _ t
    uᴰ : Tmᴰ _ _ _ u
    vᴰ : Tmᴰ _ _ _ v
    πᴰ : #∈ᴰ _ π

  infix 4 _≡Subᴰ[_]_
  _≡Subᴰ[_]_ : ∀ {Γᴰ : Conᴰ Γ} {Δᴰ : Conᴰ Δ} {σ τ : Sub Γ Δ}
    → Subᴰ Γᴰ Δᴰ σ → σ ≡ τ → Subᴰ Γᴰ Δᴰ τ → Prop
  _≡Subᴰ[_]_ {Γᴰ = Γᴰ} {Δᴰ = Δᴰ} σᴰ p τᴰ = coe (cong (Subᴰ Γᴰ Δᴰ) p) σᴰ ≡ τᴰ

  infix 4 _≡Tyᴰ[_]_
  _≡Tyᴰ[_]_ : ∀ {Γᴰ : Conᴰ Γ} {A B : Ty Γ}
    → Tyᴰ Γᴰ A → A ≡ B → Tyᴰ Γᴰ B → Prop
  _≡Tyᴰ[_]_ {Γᴰ = Γᴰ} Aᴰ p Bᴰ = coe (cong (Tyᴰ Γᴰ) p) Aᴰ ≡ Bᴰ

  infix 4 _≡#∈ᴰ[_]_
  _≡#∈ᴰ[_]_ : ∀ {Γᴰ : Conᴰ Γ} {π ρ : #∈ Γ}
    → #∈ᴰ Γᴰ π → π ≡ ρ → #∈ᴰ Γᴰ ρ → Prop
  _≡#∈ᴰ[_]_ {Γᴰ = Γᴰ} πᴰ p ρᴰ = coe (cong (#∈ᴰ Γᴰ) p) πᴰ ≡ ρᴰ

  infix 4 _≡Tmᴰ[_,_,_]_
  _≡Tmᴰ[_,_,_]_ : ∀ {Γᴰ : Conᴰ Γ} {A B : Ty Γ} {Aᴰ : Tyᴰ Γᴰ A} {Bᴰ : Tyᴰ Γᴰ B}
      {t : Tm Γ i A} {u : Tm Γ i B}
    → Tmᴰ Γᴰ i Aᴰ t
    → (p : A ≡ B)
    → Aᴰ ≡[ cong (Tyᴰ Γᴰ) p ] Bᴰ
    → t ≡[ cong (Tm Γ i) p ] u
    → Tmᴰ Γᴰ i Bᴰ u
    → Prop
  _≡Tmᴰ[_,_,_]_ {Γᴰ = Γᴰ} {Aᴰ = Aᴰ} {t = t} tᴰ p pᴰ q uᴰ = {!!}
    -- coe (cong2' {I = Ty _} {A = Tyᴰ Γᴰ} {B = Tm _ _} (Tmᴰ Γᴰ _) p pᴰ q) tᴰ ≡ uᴰ

  -- Displayed symmetry for Tyᴰ
  symTyᴰ : ∀ {Γᴰ : Conᴰ Γ} {A B : Ty Γ} {Aᴰ : Tyᴰ Γᴰ A} {Bᴰ : Tyᴰ Γᴰ B}
    → (p : A ≡ B)
    → Aᴰ ≡Tyᴰ[ p ] Bᴰ
    → Bᴰ ≡Tyᴰ[ sym p ] Aᴰ
  symTyᴰ {Γᴰ = Γᴰ} p = {!!}

  record CwFwEᴰ-core (c : CwFwE-core) : Set where
    open CwFwE-core c
    field
      idᴰ : Subᴰ Γᴰ Γᴰ id
      _∘ᴰ_ : Subᴰ Δᴰ Θᴰ σ → Subᴰ Γᴰ Δᴰ τ → Subᴰ Γᴰ Θᴰ (σ ∘ τ)
      assocᴰ : ρᴰ ∘ᴰ (σᴰ ∘ᴰ τᴰ) ≡Subᴰ[ assoc ] (ρᴰ ∘ᴰ σᴰ) ∘ᴰ τᴰ
      ∘idᴰ : idᴰ ∘ᴰ σᴰ ≡Subᴰ[ ∘id ] σᴰ
      id∘ᴰ : σᴰ ∘ᴰ idᴰ ≡Subᴰ[ id∘ ] σᴰ

      ∙ᴰ : Conᴰ ∙
      εᴰ : Subᴰ Γᴰ ∙ᴰ ε
      ∃!εᴰ : εᴰ {Γᴰ = Γᴰ} ≡Subᴰ[ ∃!ε ] σᴰ

      _[_]Tᴰ : Tyᴰ Δᴰ A → Subᴰ Γᴰ Δᴰ σ → Tyᴰ Γᴰ (A [ σ ]T)
      _[_]ᴰ : Tmᴰ Δᴰ i Aᴰ t → (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Tmᴰ Γᴰ i (Aᴰ [ σᴰ ]Tᴰ) (t [ σ ])
      _[_]#ᴰ : #∈ᴰ Δᴰ π → Subᴰ Γᴰ Δᴰ σ → #∈ᴰ Γᴰ (π [ σ ]#)
      [id]Tᴰ : Aᴰ [ idᴰ ]Tᴰ ≡Tyᴰ[ [id]T ] Aᴰ
      [id]ᴰ : (tᴰ [ idᴰ ]ᴰ) ≡Tmᴰ[ [id]T , [id]Tᴰ , [id] ] tᴰ
      [id]#ᴰ : πᴰ [ idᴰ ]#ᴰ ≡#∈ᴰ[ [id]# ] πᴰ
      [∘]Tᴰ : Aᴰ [ σᴰ ∘ᴰ τᴰ ]Tᴰ ≡Tyᴰ[ [∘]T ] (Aᴰ [ σᴰ ]Tᴰ) [ τᴰ ]Tᴰ
      [∘]ᴰ : (tᴰ [ σᴰ ∘ᴰ τᴰ ]ᴰ) ≡Tmᴰ[ [∘]T , [∘]Tᴰ , [∘] ] ((tᴰ [ σᴰ ]ᴰ) [ τᴰ ]ᴰ)
      [∘]#ᴰ : πᴰ [ σᴰ ∘ᴰ τᴰ ]#ᴰ ≡#∈ᴰ[ [∘]# ] (πᴰ [ σᴰ ]#ᴰ) [ τᴰ ]#ᴰ

    -- coeTmᴰ : ∀ {Aᴰ : Tyᴰ Γᴰ A} {Bᴰ : Tyᴰ Γᴰ B} (p : A ≡ B)
    --   → Aᴰ ≡Tyᴰ[ p ] Bᴰ → Tmᴰ Γᴰ i Aᴰ t → Tmᴰ Γᴰ i Bᴰ (coeTm p t)
    -- coeTmᴰ p pᴰ tᴰ = coe (cong2' {I = Ty _} {A = Tyᴰ _} {B = Tm _ _} (Tmᴰ _ _) p pᴰ refl) tᴰ

    -- -- Convert displayed substitution equality to displayed type equality via substitution
    -- congTyᴰ[] : ∀ {A : Ty Δ} {Γᴰ : Conᴰ Γ} {Δᴰ : Conᴰ Δ} {Aᴰ : Tyᴰ Δᴰ A}
    --               {σᴰ : Subᴰ Γᴰ Δᴰ σ} {τᴰ : Subᴰ Γᴰ Δᴰ τ}
    --   → (p : σ ≡ τ)
    --   → σᴰ ≡Subᴰ[ p ] τᴰ
    --   → Aᴰ [ σᴰ ]Tᴰ ≡Tyᴰ[ cong (A [_]T) p ] Aᴰ [ τᴰ ]Tᴰ
    -- congTyᴰ[] {A = A} {Γᴰ = Γᴰ} {Aᴰ = Aᴰ} p pᴰ =
    --   {!!}

    -- field
    --   _▷ᴰ[_]_ : (Γᴰ : Conᴰ Γ) → (i : Mode) → Tyᴰ Γᴰ A → Conᴰ (Γ ▷[ i ] A)
    --   pᴰ : Subᴰ (Γᴰ ▷ᴰ[ i ] Aᴰ) Γᴰ p
    --   qᴰ : Tmᴰ (Γᴰ ▷ᴰ[ i ] Aᴰ) i (Aᴰ [ pᴰ ]Tᴰ) q
    --   _,,ᴰ_ : (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Tmᴰ Γᴰ i (Aᴰ [ σᴰ ]Tᴰ) t → Subᴰ Γᴰ (Δᴰ ▷ᴰ[ i ] Aᴰ) (σ ,, t)
    --   ,∘ᴰ : {Γᴰ : Conᴰ Γ} {Δᴰ : Conᴰ Δ} {Aᴰ : Tyᴰ Δᴰ A} {Θᴰ : Conᴰ Θ}
    --         {σᴰ : Subᴰ Γᴰ Δᴰ σ} {ρᴰ : Subᴰ Θᴰ Γᴰ ρ}
    --         {tᴰ : Tmᴰ Γᴰ i (Aᴰ [ σᴰ ]Tᴰ) t}
    --     → (σᴰ ,,ᴰ tᴰ) ∘ᴰ ρᴰ ≡Subᴰ[ ,∘ ]
    --       (σᴰ ∘ᴰ ρᴰ) ,,ᴰ coeTmᴰ (sym [∘]T) (symTyᴰ [∘]T [∘]Tᴰ) (tᴰ [ ρᴰ ]ᴰ)
    --   p,qᴰ : pᴰ {Γᴰ = Γᴰ} {i = i} {Aᴰ = Aᴰ} ,,ᴰ qᴰ ≡Subᴰ[ p,q ] idᴰ
    --   p∘,ᴰ : {tᴰ : Tmᴰ Γᴰ i (Aᴰ [ σᴰ ]Tᴰ) t} → pᴰ ∘ᴰ (σᴰ ,,ᴰ tᴰ) ≡Subᴰ[ p∘, ] σᴰ
    --   q[,]ᴰ : {Γᴰ : Conᴰ Γ} {Δᴰ : Conᴰ Δ} {Aᴰ : Tyᴰ Δᴰ A}
    --           {σᴰ : Subᴰ Γᴰ Δᴰ σ} {tᴰ : Tmᴰ Γᴰ i (Aᴰ [ σᴰ ]Tᴰ) t}
    --     → qᴰ [ σᴰ ,,ᴰ tᴰ ]ᴰ
    --       ≡Tmᴰ[ trans (sym [∘]T) (cong (A [_]T) p∘,)
    --           , trans ({! symTyᴰ [∘]T [∘]Tᴰ!}) ({!!})
    --           , q[,] ]
    --       tᴰ

    --   _▷#ᴰ : Conᴰ Γ → Conᴰ (Γ ▷#)
    --   p#ᴰ : Subᴰ (Γᴰ ▷#ᴰ) Γᴰ p#
    --   q#ᴰ : #∈ᴰ (Γᴰ ▷#ᴰ) q#
    --   _,#ᴰ_ : Subᴰ Γᴰ Δᴰ σ → #∈ᴰ Γᴰ π → Subᴰ Γᴰ (Δᴰ ▷#ᴰ) (σ ,# π)
    --   ,#∘ᴰ : (σᴰ ,#ᴰ πᴰ) ∘ᴰ ρᴰ ≡[ cong (Subᴰ Θᴰ (Δᴰ ▷#ᴰ)) ,#∘ ] (σᴰ ∘ᴰ ρᴰ) ,#ᴰ (πᴰ [ ρᴰ ]#ᴰ)
    --   p,#qᴰ : p#ᴰ {Γᴰ = Γᴰ} ,#ᴰ q#ᴰ ≡[ cong (Subᴰ (Γᴰ ▷#ᴰ) (Γᴰ ▷#ᴰ)) p,#q ] idᴰ
    --   p∘,#ᴰ : p#ᴰ ∘ᴰ (σᴰ ,#ᴰ πᴰ) ≡[ cong (Subᴰ Γᴰ Δᴰ) p∘,# ] σᴰ
    --   q[,#]ᴰ : q#ᴰ [ σᴰ ,#ᴰ πᴰ ]#ᴰ ≡[ cong (#∈ᴰ Γᴰ) q[,#] ] πᴰ

    -- ⟨_⟩ᴰ : (tᴰ : Tmᴰ Γᴰ i Aᴰ t) → Subᴰ Γᴰ (Γᴰ ▷ᴰ[ i ] Aᴰ) ⟨ t ⟩
    -- ⟨ tᴰ ⟩ᴰ = idᴰ ,,ᴰ (tᴰ [ idᴰ ]ᴰ)

    -- _⁺ᴰ : (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Subᴰ (Γᴰ ▷ᴰ[ i ] (Aᴰ [ σᴰ ]Tᴰ)) (Δᴰ ▷ᴰ[ i ] Aᴰ) (σ ⁺)
    -- σᴰ ⁺ᴰ = (σᴰ ∘ᴰ pᴰ) ,,ᴰ coeTmᴰ (sym [∘]T) (sym [∘]Tᴰ) qᴰ

    -- _⁺#ᴰ : (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Subᴰ (Γᴰ ▷#ᴰ) (Δᴰ ▷#ᴰ) (σ ⁺#)
    -- σᴰ ⁺#ᴰ = (σᴰ ∘ᴰ p#ᴰ) ,#ᴰ q#ᴰ

    -- field
    --   ↓ᴰ : Tmᴰ (Γᴰ ▷#ᴰ) ω (Aᴰ [ p#ᴰ ]Tᴰ) t → Tmᴰ Γᴰ z Aᴰ (↓ t)
    --   ↑ᴰ : Tmᴰ Γᴰ z Aᴰ t → Tmᴰ (Γᴰ ▷#ᴰ) ω (Aᴰ [ p#ᴰ ]Tᴰ) (↑ t)
    --   -- ↓[]ᴰ : (↓ᴰ tᴰ) [ σᴰ ]ᴰ ≡[ cong2i (Tmᴰ Γᴰ z) (cong (↓_ {A = A}) (cong (coeTm _) refl)) refl ]
    --   --   ↓ᴰ (coeTmᴰ (trans (sym [∘]T) (trans (cong (A [_]T) p∘,#) [∘]T))
    --   --              (trans (sym [∘]Tᴰ) (trans (cong (Aᴰ [_]Tᴰ) p∘,#ᴰ) [∘]Tᴰ))
    --   --              (tᴰ [ σᴰ ⁺#ᴰ ]ᴰ))
    --   ↑↓ᴰ : ↑ᴰ (↓ᴰ tᴰ) ≡[ cong (Tmᴰ (Γᴰ ▷#ᴰ) ω (Aᴰ [ p#ᴰ ]Tᴰ)) ↑↓ ] tᴰ
    --   ↓↑ᴰ : ↓ᴰ (↑ᴰ tᴰ) ≡[ cong (Tmᴰ Γᴰ z Aᴰ) ↓↑ ] tᴰ

    -- pz'ᴰ : Subᴰ (Γᴰ ▷ᴰ[ ω ] Aᴰ) (Γᴰ ▷ᴰ[ z ] Aᴰ) pz'
    -- pz'ᴰ = pᴰ ,,ᴰ ↓ᴰ (qᴰ [ p#ᴰ ]ᴰ)

    -- field
    --   pz∘⁺≡⁺∘pz'ᴰ : (_⁺ᴰ {Γᴰ = Γᴰ} {Aᴰ = Aᴰ} σᴰ) ∘ᴰ pz'ᴰ {Γᴰ = Γᴰ}
    --     ≡[ cong (Subᴰ (Γᴰ ▷ᴰ[ ω ] (Aᴰ [ σᴰ ]Tᴰ)) (Δᴰ ▷ᴰ[ z ] Aᴰ)) pz∘⁺≡⁺∘pz' ]
    --     pz'ᴰ ∘ᴰ (σᴰ ⁺ᴰ)

    -- ↓*ᴰ : Tmᴰ Γᴰ i Aᴰ t → Tmᴰ Γᴰ z Aᴰ (↓* t)
    -- ↓*ᴰ {i = z} tᴰ = tᴰ
    -- ↓*ᴰ {i = ω} tᴰ = ↓ᴰ (tᴰ [ p#ᴰ ]ᴰ)

    -- pzᴰ : Subᴰ (Γᴰ ▷ᴰ[ i ] Aᴰ) (Γᴰ ▷ᴰ[ z ] Aᴰ) pz
    -- pzᴰ = pᴰ ,,ᴰ ↓*ᴰ qᴰ

    -- pz∘⁺≡⁺∘pzᴰ : (_⁺ᴰ {Γᴰ = Γᴰ} {Aᴰ = Aᴰ} σᴰ) ∘ᴰ pzᴰ {Γᴰ = Γᴰ} {i = ω}
    --   ≡[ cong (Subᴰ (Γᴰ ▷ᴰ[ ω ] (Aᴰ [ σᴰ ]Tᴰ)) (Δᴰ ▷ᴰ[ z ] Aᴰ)) pz∘⁺≡⁺∘pz ]
    --   pzᴰ ∘ᴰ (σᴰ ⁺ᴰ)
    -- pz∘⁺≡⁺∘pzᴰ {Γᴰ = Γᴰ} {Aᴰ = Aᴰ} {σᴰ = σᴰ} = pz∘⁺≡⁺∘pz'ᴰ

  -- module in-CwFwE-core (c : CwFwE-core) where
  --   open CwFwE-core c

  --   record Π-structure  : Set where
  --     field
  --       Π : (i : Mode) → (A : Ty Γ) → (B : Ty (Γ ▷[ z ] A)) → Ty Γ
  --       Π[] : (Π i A B) [ σ ]T ≡ Π i (A [ σ ]T) (B [ σ ⁺ ]T)

  --       lam : (f : Tm (Γ ▷[ i ] A) ω (B [ pz ]T)) → Tm Γ ω (Π i A B)
  --       lam[] : (lam {i = i} t) [ σ ]
  --         ≡[ cong (Tm _ _) Π[] ] lam (coeTm (sym [pz][⁺]≡[⁺][pz]) (t [ σ ⁺ ]))

  --       ap : (f : Tm Γ ω (Π i A B)) → Tm (Γ ▷[ i ] A) ω (B [ pz ]T)

  --       Πβ : ap {i = i} (lam t) ≡ t
  --       Πη : lam {i = i} (ap t) ≡ t

  --   record U-structure : Set where
  --     field
  --       U : Ty Γ
  --       U[] : U [ σ ]T ≡ U

  --       El : (t : Tm Γ z U) → Ty Γ
  --       El[] : (El t) [ σ ]T ≡ El (subst (Tm _ _) U[] (t [ σ ]))

  --       code : (A : Ty Γ) → Tm Γ z U
  --       code[] : (code A) [ σ ] ≡[ cong (Tm _ _) U[] ] code (A [ σ ]T)

  --       El-code : El (code A) ≡ A
  --       code-El : code (El t) ≡ t

  --   -- Π whose bound type is relevant
  --   record Π'-structure  : Set where
  --     field
  --       Π' : (A : Ty Γ) → (B : Ty (Γ ▷[ ω ] A)) → Ty Γ
  --       Π'[] : (Π' A B) [ σ ]T ≡ Π' (A [ σ ]T) (B [ σ ⁺ ]T)

  --       lam' : (f : Tm (Γ ▷[ ω ] A) ω B) → Tm Γ ω (Π' A B)
  --       lam'[] : (lam' t) [ σ ] ≡[ cong (Tm _ _) Π'[] ] lam' (t [ σ ⁺ ])

  --       ap' : (f : Tm Γ ω (Π' A B)) → Tm (Γ ▷[ ω ] A) ω B

  --       Πβ' : ap' (lam' t) ≡ t
  --       Πη' : lam' (ap' t) ≡ t


module CwFwE-syntax where
  postulate
    syn : CwFwE

  open CwFwE syn
  open CwFwE-sorts sorts
  open in-CwFwE-sorts.CwFwE-core core

  
