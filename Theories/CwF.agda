{-# OPTIONS --type-in-type --lossy-unification #-}
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
    Γ Γ' Δ Δ' Θ Θ' : Con
    σ τ ρ : Sub _ _
    A B C : Ty _
    t u v : Tm _ _

  opaque
    unfolding coe

    ap-Subᶜ : Γ ≡ Γ' → Δ ≡ Δ' → Sub Γ Δ ≡ Sub Γ' Δ'
    ap-Subᶜ refl refl = refl

    ap-Tyᶜ : Γ ≡ Δ → Ty Γ ≡ Ty Δ
    ap-Tyᶜ refl = refl

    ap-Tm : A ≡ B → Tm Γ A ≡ Tm Γ B
    ap-Tm refl = refl

    ap-Tmᶜ : (e : Γ ≡ Δ) → A ≡[ ap-Tyᶜ e ] B → Tm Γ A ≡ Tm Δ B
    ap-Tmᶜ refl refl = refl

  module core-utils
    (_[_]T : ∀ {Γ Δ} → (A : Ty Δ) → (σ : Sub Γ Δ) → Ty Γ)
    where
    opaque
      unfolding coe

      ap-[]T₀-impl : σ ≡ τ → A [ σ ]T ≡ A [ τ ]T
      ap-[]T₀-impl refl = refl

  record CwF-core : Set where
    field
      id : Sub Γ Γ
      _∘_ : (σ : Sub Δ Θ) → (τ : Sub Γ Δ) → Sub Γ Θ
      assoc : ρ ∘ (σ ∘ τ) ≡ (ρ ∘ σ) ∘ τ
      id∘ : id ∘ σ ≡ σ
      ∘id : σ ∘ id ≡ σ

      ∙ : Con
      ε : Sub Γ ∙
      ∃!ε : ε {Γ} ≡ σ

      _[_]T : (A : Ty Δ) → (σ : Sub Γ Δ) → Ty Γ
      _[_] : (t : Tm Δ A) → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
      [id]T : A [ id ]T ≡ A
      [id] : t [ id ] ≡[ ap-Tm [id]T ] t
      [∘]T : A [ σ ∘ τ ]T ≡ (A [ σ ]T) [ τ ]T
      [∘] : t [ σ ∘ τ ] ≡[ ap-Tm [∘]T ] (t [ σ ]) [ τ ]

    ap-[]T₀ : σ ≡ τ → A [ σ ]T ≡ A [ τ ]T
    ap-[]T₀ = core-utils.ap-[]T₀-impl _[_]T

    field
      -- Context extension
      _▷_ : (Γ : Con) → (A : Ty Γ) → Con
      p : Sub (Γ ▷ A) Γ
      q : Tm (Γ ▷ A) (A [ p ]T)
      _,,_ : (σ : Sub Γ Δ) → (t : Tm Γ (A [ σ ]T)) → Sub Γ (Δ ▷ A)
      ,∘ : (σ ,, t) ∘ ρ ≡ (σ ∘ ρ) ,, coe (ap-Tm (sym [∘]T)) (t [ ρ ])
      p,q : p {Γ} {A} ,, q ≡ id
      p∘, : p ∘ (σ ,, t) ≡ σ
      q[,] : q [ σ ,, t ] ≡[ ap-Tm (trans (sym [∘]T) (ap-[]T₀ p∘,)) ] t


    ⟨_⟩ : (t : Tm Γ A) → Sub Γ (Γ ▷ A)
    ⟨ t ⟩ = id ,, (t [ id ])

    _⁺ : (σ : Sub Γ Δ) → Sub (Γ ▷ (A [ σ ]T)) (Δ ▷ A)
    σ ⁺ = (σ ∘ p) ,, coe (ap-Tm (sym [∘]T)) q

    -- Congruence rules
    opaque
      unfolding coe

      ap-▷ : (p : Γ ≡ Γ') → A ≡[ ap-Tyᶜ p ] B → (Γ ▷ A) ≡ (Γ' ▷ B)
      ap-▷ refl refl = refl

      ap-id : (p : Γ ≡ Γ') → id {Γ} ≡[ ap-Subᶜ p p ] id {Γ'}
      ap-id refl = refl

      ap-ε : (p : Γ ≡ Γ') → ε {Γ} ≡[ ap-Subᶜ p refl ] ε {Γ'}
      ap-ε refl = refl

      ap-∘ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ Θ₁ Θ₂} (p : Γ₁ ≡ Γ₂) (q : Δ₁ ≡ Δ₂) (r : Θ₁ ≡ Θ₂)
        {σ₁ : Sub Γ₁ Δ₁} {σ₂ : Sub Γ₂ Δ₂} {τ₁ : Sub Θ₁ Γ₁} {τ₂ : Sub Θ₂ Γ₂}
        → σ₁ ≡[ ap-Subᶜ p q ] σ₂
        → τ₁ ≡[ ap-Subᶜ r p ] τ₂
        → σ₁ ∘ τ₁ ≡[ ap-Subᶜ r q ] σ₂ ∘ τ₂
      ap-∘ refl refl refl refl refl = refl

      ap-[]T : (q : Δ ≡ Δ') (p : Γ ≡ Γ') → A ≡[ ap-Tyᶜ p ] B → σ ≡[ ap-Subᶜ q p ] τ
        → (A [ σ ]T) ≡[ ap-Tyᶜ q ] (B [ τ ]T)
      ap-[]T refl refl refl refl = refl

      ap-[] : (q : Δ ≡ Δ') (p : Γ ≡ Γ')
        → (prA : A ≡[ ap-Tyᶜ p ] B)
        → (prσ : σ ≡[ ap-Subᶜ q p ] τ)
        → t ≡[ ap-Tmᶜ p prA ] u
        → (t [ σ ]) ≡[ ap-Tmᶜ q (ap-[]T q p prA prσ) ] (u [ τ ])
      ap-[] refl refl refl refl refl = refl

      ap-p : (prΓ : Γ ≡ Γ') → (prA : A ≡[ ap-Tyᶜ prΓ ] B)
        → p {Γ} {A} ≡[ ap-Subᶜ (ap-▷ prΓ prA) prΓ ] p {Γ'} {B}
      ap-p refl refl = refl

      ap-q : (prΓ : Γ ≡ Γ') → (prA : A ≡[ ap-Tyᶜ prΓ ] B)
        → q {Γ} {A} ≡[ ap-Tmᶜ (ap-▷ prΓ prA) (ap-[]T (ap-▷ prΓ prA) prΓ prA (ap-p prΓ prA)) ] q {Γ'} {B}
      ap-q refl refl = refl

      ap-,, : (p : Γ ≡ Γ') (q : Δ ≡ Δ')
        {t : Tm Γ (A [ σ ]T)} {t' : Tm Γ' (B [ τ ]T)}
        → (prσ : σ ≡[ ap-Subᶜ p q ] τ)
        → (prA : A ≡[ ap-Tyᶜ q ] B)
        → t ≡[ ap-Tmᶜ p (ap-[]T p q prA prσ) ] t'
        → (σ ,, t) ≡[ ap-Subᶜ p (ap-▷ q prA) ] (τ ,, t')
      ap-,, refl refl refl refl refl = refl

  module in-CwF-core (c : CwF-core) where
    open CwF-core c

    record Π-structure  : Set where
      field
        Π : (A : Ty Γ) → (B : Ty (Γ ▷ A)) → Ty Γ
        Π[] : (Π A B) [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ⁺ ]T)

        lam : (f : Tm (Γ ▷ A) B) → Tm Γ (Π A B)
        lam[] : (lam t) [ σ ] ≡[ ap-Tm Π[] ] lam (t [ σ ⁺ ])

        ap : (f : Tm Γ (Π A B)) → Tm (Γ ▷ A) B

        Πβ : ap (lam t) ≡ t
        Πη : lam (ap t) ≡ t

      _⇒_ : Ty Γ → Ty Γ → Ty Γ
      A ⇒ B = Π A (B [ p ]T)

    record U-structure : Set where
      field
        U : Ty Γ
        U[] : U [ σ ]T ≡ U

        El : (t : Tm Γ U) → Ty Γ
        El[] : (El t) [ σ ]T ≡ El (coe (ap-Tm U[]) (t [ σ ]))

        code : (A : Ty Γ) → Tm Γ U
        code[] : (code A) [ σ ] ≡[ ap-Tm U[] ] code (A [ σ ]T)

        El-code : El (code A) ≡ A
        code-El : code (El t) ≡ t



record CwF : Set where
  field
    sorts : CwF-sorts
  open in-CwF-sorts sorts
  field
    core : CwF-core
  open in-CwF-core core
  field
    Π-str : Π-structure
    U-str : U-structure

-- Displayed CwF

record CwFᴰ-sorts (s : CwF-sorts) : Set where
  open CwF-sorts s
  field
    Conᴰ : Con → Set
    Subᴰ : ∀ {Γ Δ} → Conᴰ Γ → Conᴰ Δ → Sub Γ Δ → Set
    Tyᴰ : ∀ {Γ} → Conᴰ Γ → Ty Γ → Set
    Tmᴰ : ∀ {Γ A} → (Γᴰ : Conᴰ Γ) → Tyᴰ Γᴰ A → Tm Γ A → Set

module in-CwFᴰ-sorts {s : CwF-sorts} (sᴰ : CwFᴰ-sorts s) (c : in-CwF-sorts.CwF-core s) where
  open CwF-sorts s
  open CwFᴰ-sorts sᴰ
  open in-CwF-sorts s
  open CwF-core c
  variable
    Γᴰ Γᴰ' Δᴰ Δᴰ' Θᴰ : Conᴰ Γ
    σᴰ σᴰ' τᴰ τᴰ' ρᴰ : Subᴰ Γᴰ Δᴰ σ
    Aᴰ Aᴰ' Bᴰ Cᴰ : Tyᴰ Γᴰ A
    tᴰ tᴰ' uᴰ uᴰ' vᴰ : Tmᴰ Γᴰ Aᴰ t

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

    ap-Tmᴰ : (p : A ≡ B)
      → Aᴰ ≡[ ap-Tyᴰ p ] Bᴰ
      → t ≡[ ap-Tm p ] u
      → Tmᴰ Γᴰ Aᴰ t ≡ Tmᴰ Γᴰ Bᴰ u
    ap-Tmᴰ refl refl refl = refl

    ap-Tmᴰᶜ : (pΓ : Γ ≡ Δ) → (pA : A ≡[ ap-Tyᶜ pΓ ] B)
      → (pΓᴰ : Γᴰ ≡[ ap-Conᴰᶜ pΓ ] Δᴰ)
      → Aᴰ ≡[ ap-Tyᴰᶜ pΓ pΓᴰ pA ] Bᴰ
      → t ≡[ ap-Tmᶜ pΓ pA ] u
      → Tmᴰ Γᴰ Aᴰ t ≡ Tmᴰ Δᴰ Bᴰ u
    ap-Tmᴰᶜ refl refl refl refl refl = refl

  module core-utilsᴰ
    (_[_]Tᴰ : ∀ {Γ Δ A σ} {Γᴰ : Conᴰ Γ} {Δᴰ : Conᴰ Δ}
      → Tyᴰ Δᴰ A → Subᴰ Γᴰ Δᴰ σ → Tyᴰ Γᴰ (A [ σ ]T))
    where
    opaque
      unfolding ap-Subᴰ ap-Tyᴰ
      ap-[]T₀ᴰ : (p : σ ≡ τ) → σᴰ ≡[ ap-Subᴰ p ] τᴰ
        → Aᴰ [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ (ap-[]T₀ p) ] Aᴰ [ τᴰ ]Tᴰ
      ap-[]T₀ᴰ refl refl = refl

  record CwFᴰ-core : Set where
    field
      idᴰ : {Γᴰ : Conᴰ Γ} → Subᴰ Γᴰ Γᴰ id
      _∘ᴰ_ : Subᴰ Δᴰ Θᴰ σ → Subᴰ Γᴰ Δᴰ τ → Subᴰ Γᴰ Θᴰ (σ ∘ τ)
      assocᴰ : ρᴰ ∘ᴰ (σᴰ ∘ᴰ τᴰ) ≡[ ap-Subᴰ assoc ] (ρᴰ ∘ᴰ σᴰ) ∘ᴰ τᴰ
      id∘ᴰ : idᴰ ∘ᴰ σᴰ ≡[ ap-Subᴰ id∘ ] σᴰ
      ∘idᴰ : σᴰ ∘ᴰ idᴰ ≡[ ap-Subᴰ ∘id ] σᴰ

      ∙ᴰ : Conᴰ ∙
      εᴰ : Subᴰ Γᴰ ∙ᴰ ε
      ∃!εᴰ : εᴰ {Γᴰ = Γᴰ} ≡[ ap-Subᴰ ∃!ε ] σᴰ

      _[_]Tᴰ : Tyᴰ Δᴰ A → Subᴰ Γᴰ Δᴰ σ → Tyᴰ Γᴰ (A [ σ ]T)
      _[_]ᴰ : Tmᴰ Δᴰ Aᴰ t → (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Tmᴰ Γᴰ (Aᴰ [ σᴰ ]Tᴰ) (t [ σ ])
      [id]Tᴰ : Aᴰ [ idᴰ ]Tᴰ ≡[ ap-Tyᴰ [id]T ] Aᴰ
      [id]ᴰ : {tᴰ : Tmᴰ Δᴰ Aᴰ t} → (tᴰ [ idᴰ ]ᴰ) ≡[ ap-Tmᴰ [id]T [id]Tᴰ [id] ] tᴰ
      [∘]Tᴰ : Aᴰ [ σᴰ ∘ᴰ τᴰ ]Tᴰ ≡[ ap-Tyᴰ [∘]T ] (Aᴰ [ σᴰ ]Tᴰ) [ τᴰ ]Tᴰ
      [∘]ᴰ : {tᴰ : Tmᴰ Δᴰ Aᴰ t} → (tᴰ [ σᴰ ∘ᴰ τᴰ ]ᴰ) ≡[ ap-Tmᴰ [∘]T [∘]Tᴰ [∘] ] ((tᴰ [ σᴰ ]ᴰ) [ τᴰ ]ᴰ)

    ap-[]T₀ᴰ : (p : σ ≡ τ) → σᴰ ≡[ ap-Subᴰ p ] τᴰ
      → Aᴰ [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ (ap-[]T₀ p) ] Aᴰ [ τᴰ ]Tᴰ
    ap-[]T₀ᴰ = core-utilsᴰ.ap-[]T₀ᴰ _[_]Tᴰ

    field
      _▷ᴰ_ : (Γᴰ : Conᴰ Γ) → Tyᴰ Γᴰ A → Conᴰ (Γ ▷ A)
      pᴰ : Subᴰ (Γᴰ ▷ᴰ Aᴰ) Γᴰ p
      qᴰ : Tmᴰ (Γᴰ ▷ᴰ Aᴰ) (Aᴰ [ pᴰ ]Tᴰ) q
      _,,ᴰ_ : (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Tmᴰ Γᴰ (Aᴰ [ σᴰ ]Tᴰ) t → Subᴰ Γᴰ (Δᴰ ▷ᴰ Aᴰ) (σ ,, t)
      ,∘ᴰ : (σᴰ ,,ᴰ tᴰ) ∘ᴰ ρᴰ ≡[ ap-Subᴰ ,∘ ]
          (σᴰ ∘ᴰ ρᴰ) ,,ᴰ coe (ap-Tmᴰ (sym [∘]T) (symᴰ [∘]Tᴰ) refl) (tᴰ [ ρᴰ ]ᴰ)
      p,qᴰ : pᴰ {Γᴰ = Γᴰ} {Aᴰ = Aᴰ} ,,ᴰ qᴰ ≡[ ap-Subᴰ p,q ] idᴰ
      p∘,ᴰ : pᴰ ∘ᴰ (σᴰ ,,ᴰ tᴰ) ≡[ ap-Subᴰ p∘, ] σᴰ
      q[,]ᴰ : {tᴰ : Tmᴰ Γᴰ (Aᴰ [ σᴰ ]Tᴰ) t} → qᴰ [ σᴰ ,,ᴰ tᴰ ]ᴰ
          ≡[ ap-Tmᴰ (trans (sym [∘]T) (ap-[]T₀ p∘,))
                    (transᴰ (symᴰ [∘]Tᴰ) (ap-[]T₀ᴰ p∘, p∘,ᴰ))
                    q[,] ]
          tᴰ

    _⁺ᴰ : (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Subᴰ (Γᴰ ▷ᴰ (Aᴰ [ σᴰ ]Tᴰ)) (Δᴰ ▷ᴰ Aᴰ) (σ ⁺)
    σᴰ ⁺ᴰ = (σᴰ ∘ᴰ pᴰ) ,,ᴰ coe (ap-Tmᴰ (sym [∘]T) (symᴰ [∘]Tᴰ) refl) qᴰ

  module in-CwFᴰ-core (cᴰ : CwFᴰ-core) where
    open CwFᴰ-core cᴰ

    record Π-structureᴰ (ps : in-CwF-sorts.in-CwF-core.Π-structure s c) : Set where
      open in-CwF-sorts.in-CwF-core.Π-structure ps
      field
        Πᴰ : (Aᴰ : Tyᴰ Γᴰ A) → (Bᴰ : Tyᴰ (Γᴰ ▷ᴰ Aᴰ) B) → Tyᴰ Γᴰ (Π A B)
        Π[]ᴰ : (Πᴰ Aᴰ Bᴰ) [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ Π[] ] Πᴰ (Aᴰ [ σᴰ ]Tᴰ) (Bᴰ [ σᴰ ⁺ᴰ ]Tᴰ)

        lamᴰ : (tᴰ : Tmᴰ (Γᴰ ▷ᴰ Aᴰ) Bᴰ t) → Tmᴰ Γᴰ (Πᴰ Aᴰ Bᴰ) (lam t)
        lamᴰ[] : (lamᴰ tᴰ) [ σᴰ ]ᴰ ≡[ ap-Tmᴰ Π[] Π[]ᴰ lam[] ] lamᴰ (tᴰ [ σᴰ ⁺ᴰ ]ᴰ)

        apᴰ : (tᴰ : Tmᴰ Γᴰ (Πᴰ Aᴰ Bᴰ) t) → Tmᴰ (Γᴰ ▷ᴰ Aᴰ) Bᴰ (ap t)

        Πβᴰ : apᴰ (lamᴰ tᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep Πβ) ] tᴰ
        Πηᴰ : lamᴰ (apᴰ tᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep Πη) ] tᴰ

    record U-structureᴰ (us : in-CwF-sorts.in-CwF-core.U-structure s c) : Set where
      open in-CwF-sorts.in-CwF-core.U-structure us
      field
        Uᴰ : Tyᴰ Γᴰ U
        U[]ᴰ : Uᴰ [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ U[] ] Uᴰ

        Elᴰ : (tᴰ : Tmᴰ Γᴰ Uᴰ t) → Tyᴰ Γᴰ (El t)
        El[]ᴰ : (Elᴰ tᴰ) [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ El[] ] Elᴰ (coe (ap-Tmᴰ U[] U[]ᴰ refl) (tᴰ [ σᴰ ]ᴰ))

        codeᴰ : (Aᴰ : Tyᴰ Γᴰ A) → Tmᴰ Γᴰ Uᴰ (code A)
        code[]ᴰ : (codeᴰ Aᴰ) [ σᴰ ]ᴰ ≡[ ap-Tmᴰ U[] U[]ᴰ code[] ] codeᴰ (Aᴰ [ σᴰ ]Tᴰ)

        El-codeᴰ : Elᴰ (codeᴰ Aᴰ) ≡[ ap-Tyᴰ El-code ] Aᴰ
        code-Elᴰ : codeᴰ (Elᴰ tᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep code-El) ] tᴰ

record CwFᴰ (base : CwF) : Set where
  open CwF base
  field
    sortsᴰ : CwFᴰ-sorts sorts
  open in-CwFᴰ-sorts sortsᴰ core
  field
    coreᴰ : CwFᴰ-core
  open in-CwFᴰ-core coreᴰ
  field
    Π-strᴰ : Π-structureᴰ Π-str
    U-strᴰ : U-structureᴰ U-str

-- Syntax (initial CwF)
module CwF-syntax where
  postulate syn : CwF
  open CwF syn public
  open CwF-sorts sorts public
  open in-CwF-sorts sorts public
  open in-CwF-sorts.CwF-core core public
  open in-CwF-sorts.in-CwF-core sorts core public
  open in-CwF-sorts.in-CwF-core.U-structure U-str public
  open in-CwF-sorts.in-CwF-core.Π-structure Π-str public

  -- Eliminator
  module CwF-elim (methods : CwFᴰ syn) where
    open CwFᴰ methods
    open CwFᴰ-sorts sortsᴰ
    open in-CwFᴰ-sorts sortsᴰ core
    open in-CwFᴰ-sorts.CwFᴰ-core coreᴰ
    open in-CwFᴰ-sorts.in-CwFᴰ-core sortsᴰ core coreᴰ

    postulate
       ⟦_⟧ᶜ : (Γ : Con) → Conᴰ Γ
       ⟦_⟧ˢ : (σ : Sub Γ Δ) → Subᴰ ⟦ Γ ⟧ᶜ ⟦ Δ ⟧ᶜ σ
       ⟦_⟧ᵀ : (A : Ty Γ) → Tyᴰ ⟦ Γ ⟧ᶜ A
       ⟦_⟧ᵗ : (a : Tm Γ A) → Tmᴰ ⟦ Γ ⟧ᶜ ⟦ A ⟧ᵀ a

    postulate
       ⟦∙⟧ : ⟦ ∙ ⟧ᶜ ≡ ∙ᴰ
       {-# REWRITE ⟦∙⟧ #-}

       ⟦id⟧ : ⟦ id {Γ} ⟧ˢ ≡ idᴰ
       {-# REWRITE ⟦id⟧ #-}

       ⟦∘⟧ : ⟦ σ ∘ τ ⟧ˢ ≡ ⟦ σ ⟧ˢ ∘ᴰ ⟦ τ ⟧ˢ
       {-# REWRITE ⟦∘⟧ #-}

       ⟦ε⟧ : ⟦ ε {Γ} ⟧ˢ ≡ εᴰ
       {-# REWRITE ⟦ε⟧ #-}

       ⟦▷⟧ : ⟦ Γ ▷ A ⟧ᶜ ≡ ⟦ Γ ⟧ᶜ ▷ᴰ ⟦ A ⟧ᵀ
       {-# REWRITE ⟦▷⟧ #-}

       ⟦[]T⟧ : ⟦ A [ σ ]T ⟧ᵀ ≡ ⟦ A ⟧ᵀ [ ⟦ σ ⟧ˢ ]Tᴰ
       {-# REWRITE ⟦[]T⟧ #-}

       ⟦p⟧ : ⟦ p {Γ} {A} ⟧ˢ ≡ pᴰ
       {-# REWRITE ⟦p⟧ #-}

       ⟦[]⟧ : ⟦ t [ σ ] ⟧ᵗ ≡ (⟦ t ⟧ᵗ [ ⟦ σ ⟧ˢ ]ᴰ)
       {-# REWRITE ⟦[]⟧ #-}

       ⟦q⟧ : ⟦ q {Γ} {A} ⟧ᵗ ≡ qᴰ
       {-# REWRITE ⟦q⟧ #-}

       ⟦,,⟧ : ⟦ σ ,, t ⟧ˢ ≡ ⟦ σ ⟧ˢ ,,ᴰ ⟦ t ⟧ᵗ
       {-# REWRITE ⟦,,⟧ #-}

    open Π-structureᴰ Π-strᴰ
    open U-structureᴰ U-strᴰ

    postulate
       ⟦Π⟧ : ⟦ Π A B ⟧ᵀ ≡ Πᴰ ⟦ A ⟧ᵀ ⟦ B ⟧ᵀ
       {-# REWRITE ⟦Π⟧ #-}

       ⟦lam⟧ : ⟦ lam t ⟧ᵗ ≡ lamᴰ ⟦ t ⟧ᵗ
       {-# REWRITE ⟦lam⟧ #-}

       ⟦ap⟧ : ⟦ ap t ⟧ᵗ ≡ apᴰ ⟦ t ⟧ᵗ
       {-# REWRITE ⟦ap⟧ #-}

       ⟦U⟧ : ⟦ U {Γ} ⟧ᵀ ≡ Uᴰ
       {-# REWRITE ⟦U⟧ #-}

       ⟦El⟧ : ⟦ El t ⟧ᵀ ≡ Elᴰ ⟦ t ⟧ᵗ
       {-# REWRITE ⟦El⟧ #-}

       ⟦code⟧ : ⟦ code A ⟧ᵗ ≡ codeᴰ ⟦ A ⟧ᵀ
       {-# REWRITE ⟦code⟧ #-}

-- Uniform model: any CwF n gives a displayed CwF over any CwF m
module CwF-uniform (m : CwF) (n : CwF) where
  open CwF n
  open CwF-sorts (CwF.sorts n)
  open in-CwF-sorts (CwF.sorts n)
  open in-CwF-sorts.CwF-core (CwF.core n)
  open in-CwF-sorts.in-CwF-core (CwF.sorts n) (CwF.core n)
  open in-CwF-sorts.in-CwF-core.Π-structure (CwF.Π-str n)
  open in-CwF-sorts.in-CwF-core.U-structure (CwF.U-str n)
  open CwFᴰ
  open CwFᴰ-sorts
  open in-CwFᴰ-sorts
  open CwFᴰ-core
  open in-CwFᴰ-core
  open Π-structureᴰ
  open U-structureᴰ

  nᴰ-sorts : CwFᴰ-sorts (m .CwF.sorts)
  nᴰ-sorts .Conᴰ _ = Con
  nᴰ-sorts .Subᴰ Γ Δ _ = Sub Γ Δ
  nᴰ-sorts .Tyᴰ Γ _ = Ty Γ
  nᴰ-sorts .Tmᴰ Γ A _ = Tm Γ A

  nᴰ-core : CwFᴰ-core nᴰ-sorts (m .CwF.core)
  nᴰ-core .idᴰ = id
  nᴰ-core ._∘ᴰ_ = _∘_
  nᴰ-core .assocᴰ = dep assoc
  nᴰ-core .∘idᴰ = dep ∘id
  nᴰ-core .id∘ᴰ = dep id∘
  nᴰ-core .∙ᴰ = ∙
  nᴰ-core .εᴰ = ε
  nᴰ-core .∃!εᴰ = dep ∃!ε
  nᴰ-core ._[_]Tᴰ = _[_]T
  nᴰ-core ._[_]ᴰ = _[_]
  nᴰ-core .[id]Tᴰ = dep [id]T
  nᴰ-core .[id]ᴰ = [id]
  nᴰ-core .[∘]Tᴰ = dep [∘]T
  nᴰ-core .[∘]ᴰ = [∘]
  nᴰ-core ._▷ᴰ_ = _▷_
  nᴰ-core .pᴰ = p
  nᴰ-core .qᴰ = q
  nᴰ-core ._,,ᴰ_ = _,,_
  nᴰ-core .,∘ᴰ = dep ,∘
  nᴰ-core .p,qᴰ = dep p,q
  nᴰ-core .p∘,ᴰ = dep p∘,
  nᴰ-core .q[,]ᴰ = q[,]

  nᴰ-Π-str : Π-structureᴰ nᴰ-sorts (m .CwF.core) nᴰ-core (m .CwF.Π-str)
  nᴰ-Π-str .Πᴰ = Π
  nᴰ-Π-str .Π[]ᴰ = dep Π[]
  nᴰ-Π-str .lamᴰ = lam
  nᴰ-Π-str .lamᴰ[] = lam[]
  nᴰ-Π-str .apᴰ = ap
  nᴰ-Π-str .Πβᴰ = dep Πβ
  nᴰ-Π-str .Πηᴰ = dep Πη

  nᴰ-U-str : U-structureᴰ nᴰ-sorts (m .CwF.core) nᴰ-core (m .CwF.U-str)
  nᴰ-U-str .Uᴰ = U
  nᴰ-U-str .U[]ᴰ = dep U[]
  nᴰ-U-str .Elᴰ = El
  nᴰ-U-str .El[]ᴰ = dep El[]
  nᴰ-U-str .codeᴰ = code
  nᴰ-U-str .code[]ᴰ = code[]
  nᴰ-U-str .El-codeᴰ = dep El-code
  nᴰ-U-str .code-Elᴰ = dep code-El

  nᴰ : CwFᴰ m
  nᴰ .CwFᴰ.sortsᴰ = nᴰ-sorts
  nᴰ .CwFᴰ.coreᴰ = nᴰ-core
  nᴰ .CwFᴰ.Π-strᴰ = nᴰ-Π-str
  nᴰ .CwFᴰ.U-strᴰ = nᴰ-U-str
