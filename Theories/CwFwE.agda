{-# OPTIONS --type-in-type --lossy-unification #-}
module Theories.CwFwE where

open import Agda.Primitive
open import Utils
open import Data.Unit renaming (⊤ to 𝟙)
open import Mode

-- Model

record CwFwE-sorts : Set where
  field
    Con : Set
    Sub : Con → Con → Set
    Ty : Con → Set
    #∈ : Con → Set
    Tm : ∀ Γ → Mode → Ty Γ → Set
    #-prop : ∀ {Γ} (p q : #∈ Γ) → p ≡ q

module in-CwFwE-sorts (s : CwFwE-sorts) where
  open CwFwE-sorts s
  variable
    Γ Γ' Δ Δ' Θ Θ' : Con
    σ σ' τ τ' ρ : Sub Γ Δ
    A A' B B' C : Ty Γ
    t t' u u' v : Tm Γ i A
    π π' ξ : #∈ Γ

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

    ap-Tmᶜ' : (e : Γ ≡ Γ') → i ≡ j →  A ≡[ ap-Tyᶜ e ] A' → Tm Γ i A ≡ Tm Γ' j A'
    ap-Tmᶜ' refl refl refl = refl


  module core-utils
    (_[_]T : ∀ {Γ Δ} → (A : Ty Δ) → (σ : Sub Γ Δ) → Ty Γ)
    (_[_] : ∀ {Γ Δ i A} → (a : Tm Δ i A) → (σ : Sub Γ Δ) → Tm Γ i (A [ σ ]T))
    where
    opaque
      unfolding coe

      ap-[]T₀-impl : σ ≡ τ → A [ σ ]T ≡ A [ τ ]T
      ap-[]T₀-impl refl = refl
      
      ap-[]T₁-impl : A ≡ B → A [ σ ]T ≡ B [ σ ]T
      ap-[]T₁-impl refl = refl

  record CwFwE-core : Set where
    field
      id : Sub Γ Γ
      _∘_ : (σ : Sub Δ Θ) → (τ : Sub Γ Δ) → Sub Γ Θ
      assoc : ρ ∘ (σ ∘ τ) ≡ (ρ ∘ σ) ∘ τ
      id∘ : id ∘ σ ≡ σ
      ∘id : σ ∘ id ≡ σ

      ∙ : Con
      ε : Sub Γ ∙
      ∃!ε : ε {Γ} ≡ σ

      -- All the equations on the #∈_ sort are technically unnecessary
      -- because it is a proposition, but we include them here anyway.

      _[_]T : (A : Ty Δ) → (σ : Sub Γ Δ) → Ty Γ
      _[_] : (t : Tm Δ i A) → (σ : Sub Γ Δ) → Tm Γ i (A [ σ ]T)
      _[_]# : (t : #∈ Δ) → (σ : Sub Γ Δ) → #∈ Γ
      [id]T : A [ id ]T ≡ A
      [id] : (t [ id ]) ≡[ ap-Tm {i = i} [id]T ] t
      [id]# : π [ id ]# ≡ π 
      [∘]T : A [ σ ∘ τ ]T ≡ (A [ σ ]T) [ τ ]T
      [∘] : t [ σ ∘ τ ] ≡[ ap-Tm {i = i} [∘]T ] ((t [ σ ]) [ τ ])
      [∘]# : π [ σ ∘ τ ]# ≡ (π [ σ ]#) [ τ ]#
      
      -- Context extension for terms
      _▷[_]_ : (Γ : Con) → Mode → (A : Ty Γ) → Con

    ap-[]T₀ : σ ≡ τ → A [ σ ]T ≡ A [ τ ]T
    ap-[]T₀ = core-utils.ap-[]T₀-impl _[_]T _[_]

    ap-[]T₁ : A ≡ B → A [ σ ]T ≡ B [ σ ]T
    ap-[]T₁ = core-utils.ap-[]T₁-impl _[_]T _[_]

    field
      p : Sub (Γ ▷[ i ] A) Γ
      q : Tm (Γ ▷[ i ] A) i (A [ p ]T)
      _,,_ : (σ : Sub Γ Δ) → (t : Tm Γ i (A [ σ ]T)) → Sub Γ (Δ ▷[ i ] A)
      ,∘ : (σ ,, t) ∘ ρ ≡ (σ ∘ ρ) ,, coe (ap-Tm {i = i} (sym [∘]T)) (t [ ρ ])
      p,q : p {Γ} {i} {A} ,, q ≡ id
      p∘, : p {Γ} {i} {A} ∘ (σ ,, t) ≡ σ
      q[,] : q [ σ ,, t ] ≡[ ap-Tm {i = i} (trans (sym [∘]T) (ap-[]T₀ p∘,)) ] t

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

      ↓[] : (↓ t) [ σ ] ≡ ↓
        (coe (ap-Tm (trans (sym [∘]T) (trans (ap-[]T₀ p∘,#) [∘]T)))
        (t [ σ ⁺# ]))  
      -- The other direction is derivable (and I will not derive it)

      ↑↓ : ↑ (↓ t) ≡ t
      ↓↑ : ↓ (↑ t) ≡ t

    -- Various congruence rules
    opaque
      unfolding coe

      ap-▷[] : (p : Γ ≡ Δ) → A ≡[ ap-Tyᶜ p ] B → (Γ ▷[ i ] A) ≡ (Δ ▷[ i ] B)
      ap-▷[] refl refl = refl

      ap-id : (p : Γ ≡ Γ') → id {Γ} ≡[ ap-Subᶜ p p ] id {Γ'}
      ap-id refl = refl

      ap-ε : (p : Γ ≡ Γ') → ε {Γ} ≡[ ap-Subᶜ p refl ] ε {Γ'}
      ap-ε refl = refl

      ap-∘ : ∀ (p : Γ ≡ Γ') (q : Δ ≡ Δ') (r : Θ ≡ Θ') {σ τ}
        → σ ≡[ ap-Subᶜ p q ] σ'
        → τ ≡[ ap-Subᶜ r p ] τ'
        → σ ∘ τ ≡[ ap-Subᶜ r q ] σ' ∘ τ'
      ap-∘ refl refl refl refl refl = refl

      ap-[]T : ∀ (q : Δ ≡ Δ') (p : Γ ≡ Γ') → A ≡[ ap-Tyᶜ p ] A' → σ ≡[ ap-Subᶜ q p ] σ' → (A [ σ ]T) ≡[ ap-Tyᶜ q ] (A' [ σ' ]T)
      ap-[]T refl refl refl refl = refl

      ap-p : (prΓ : Γ ≡ Γ')
        → (prA : A ≡[ ap-Tyᶜ prΓ ] A')
        → p {Γ} {i} {A} ≡[ ap-Subᶜ (ap-▷[] prΓ prA) prΓ ] p {Γ'} {i} {A'}
      ap-p refl refl = refl

      ap-q : ∀ (prΓ : Γ ≡ Γ')
        → (prA : A ≡[ ap-Tyᶜ prΓ ] A')
        → q {Γ} {i} {A} ≡[ ap-Tmᶜ (ap-▷[] prΓ prA) (ap-[]T (ap-▷[] prΓ prA) prΓ prA (ap-p prΓ prA) ) ] q {Γ'} {i} {A'}
      ap-q refl refl = refl

      ap-[] : ∀ (q : Δ ≡ Δ') (p : Γ ≡ Γ')
        → (prA : A ≡[ ap-Tyᶜ p ] A')
        → (prσ : σ ≡[ ap-Subᶜ q p ] σ')
        → t ≡[ ap-Tmᶜ p prA ] t'
        → (t [ σ ]) ≡[ ap-Tmᶜ q (ap-[]T q p prA prσ) ] (t' [ σ' ])
      ap-[] refl refl refl refl refl = refl

      ap-,, : ∀ (p : Γ ≡ Γ') (q : Δ ≡ Δ')
        {t : Tm Γ i (A [ σ ]T)}
        {t' : Tm Γ' i (A' [ σ' ]T) }
        → (prσ : σ ≡[ ap-Subᶜ p q ] σ')
        → (prA : A ≡[ ap-Tyᶜ q ] A')
        → t ≡[ ap-Tmᶜ p (ap-[]T p q prA prσ) ] t'
        → (σ ,, t) ≡[ ap-Subᶜ p (ap-▷[] q prA ) ] (σ' ,, t')
      ap-,, refl refl refl refl refl = refl

      ap-,# : ∀ (p : Γ ≡ Γ') (q : Δ ≡ Δ')
        → (prσ : σ ≡[ ap-Subᶜ p q ] σ')
        → π ≡[ ap-#∈ᶜ p ] π'
        → (σ ,# π) ≡[ ap-Subᶜ p (cong _▷# q) ] (σ' ,# π')
      ap-,# refl refl refl refl = refl

    opaque
      unfolding coe
      ap-[]₀ : (p : σ ≡ τ) → t [ σ ] ≡[ ap-Tm (ap-[]T₀ p) ] t [ τ ]
      ap-[]₀ refl = refl

      ap-[]₁ : ∀ {t : Tm Γ i A} {u : Tm Γ i B} (p : A ≡ B) → t ≡[ ap-Tm p ] u → t [ σ ] ≡[ ap-Tm (ap-[]T₁ p) ] u [ σ ]
      ap-[]₁ refl refl = refl

    ↑[p#] : (↑ t) [ p# ] ≡ ↑ (t [ p# ])
    ↑[p#] = ?

    opaque
      ↓* : Tm Γ i A → Tm Γ z A
      ↓* {i = z} t = t
      ↓* {i = ω} t = ↓ (t [ p# ])

      ↓*[] : {t : Tm Γ i A} → (↓* t) [ σ ] ≡ ↓* (t [ σ ])
      ↓*[] {i = z} = refl
      ↓*[] {i = ω} = trans ↓[] (cong ↓ (transᴰ (symᴰ [∘]) (transᴰ (ap-[]₀ p∘,#) [∘])))

      ↓*↑ : {t : Tm Γ z A} → ↓* (↑ t) ≡ t [ p# ]
      ↓*↑ = trans (cong ↓ ↑[p#]) ↓↑


    opaque
      unfolding ↓* coe
      ap-↓* : (p : A ≡ B) → t ≡[ ap-Tm p ] u → ↓* t ≡[ ap-Tm p ] ↓* u
      ap-↓* refl refl = refl

    opaque
      unfolding ↓*

      ↓*q[,] : (↓* {i = i} q) [ σ ,, t ] ≡[ ap-Tm (trans (sym [∘]T) (ap-[]T₀ p∘,)) ] ↓* t
      ↓*q[,] = transᴰ (dep ↓*[]) (ap-↓* (trans (sym [∘]T) (ap-[]T₀ p∘,)) q[,])

      pz : Sub (Γ ▷[ i ] A) (Γ ▷[ z ] A)
      pz = p ,, ↓* q

      p,↓*q : (p {Γ} {_} {A} ,, ↓* {i = z} q) ≡ id
      p,↓*q = p,q

      -- These lemmas are needed for lam[]
      pz∘⁺≡⁺∘pz : (_⁺ {Γ} {A = A} σ) ∘ pz {Γ} {ω} ≡ pz ∘ (σ ⁺)
      pz∘⁺≡⁺∘pz {σ = σ} = trans ,∘ (trans
        (undep (ap-,, refl refl (dep (trans (trans (sym assoc) (cong (σ ∘_) p∘,)) (sym p∘,)))
        reflᴰ (splitl (transᴰ {q = ap-Tm (ap-[]T₀ (sym p∘,))} (transᴰ (ap-[] refl refl (dep [∘]T) reflᴰ (splitl reflᴰ))
        (transᴰ q[,] (ap-↓* ( sym [∘]T) (splitr reflᴰ)))) (splitr (symᴰ ↓*q[,]))))))
        (sym ,∘))

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
    #-propᴰ : ∀ {Γ Γᴰ π π'} → (p : #∈ᴰ {Γ} Γᴰ π) (q : #∈ᴰ Γᴰ π') → (prf : π ≡ π') → p ≡[  cong (#∈ᴰ _) prf  ] q

module in-CwFwEᴰ-sorts {s : CwFwE-sorts} (sᴰ : CwFwEᴰ-sorts s) (c : in-CwFwE-sorts.CwFwE-core s) where
  open CwFwE-sorts s
  open CwFwEᴰ-sorts sᴰ
  open in-CwFwE-sorts s
  open CwFwE-core c
  open in-CwFwE-core c
  variable
    Γᴰ Γᴰ' Δᴰ Δᴰ' Θᴰ : Conᴰ Γ
    σᴰ σᴰ' τᴰ τᴰ' ρᴰ : Subᴰ Γᴰ Δᴰ σ
    Aᴰ Aᴰ' Bᴰ Cᴰ : Tyᴰ Γᴰ A
    tᴰ tᴰ' uᴰ uᴰ' vᴰ : Tmᴰ Γᴰ i Aᴰ t
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

    ap-Tmᴰᶜ' : (pΓ : Γ ≡ Δ) → (pA : A ≡[ ap-Tyᶜ pΓ ] B)
      → (pΓᴰ : Γᴰ ≡[ ap-Conᴰᶜ pΓ ] Δᴰ)
      → (pi : i ≡ j)
      → Aᴰ ≡[ ap-Tyᴰᶜ pΓ pΓᴰ pA ] Bᴰ
      → t ≡[ ap-Tmᶜ' pΓ pi pA ] u
      → Tmᴰ Γᴰ i Aᴰ t ≡ Tmᴰ Δᴰ j Bᴰ u
    ap-Tmᴰᶜ' refl refl refl refl refl refl = refl

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
      idᴰ : {Γᴰ : Conᴰ Γ} → Subᴰ Γᴰ Γᴰ id
      _∘ᴰ_ : Subᴰ Δᴰ Θᴰ σ → Subᴰ Γᴰ Δᴰ τ → Subᴰ Γᴰ Θᴰ (σ ∘ τ)
      assocᴰ : ρᴰ ∘ᴰ (σᴰ ∘ᴰ τᴰ) ≡[ ap-Subᴰ assoc ] (ρᴰ ∘ᴰ σᴰ) ∘ᴰ τᴰ
      id∘ᴰ : idᴰ ∘ᴰ σᴰ ≡[ ap-Subᴰ id∘ ] σᴰ
      ∘idᴰ : σᴰ ∘ᴰ idᴰ ≡[ ap-Subᴰ ∘id ] σᴰ

      ∙ᴰ : Conᴰ ∙
      εᴰ : Subᴰ Γᴰ ∙ᴰ ε
      ∃!εᴰ : εᴰ {Γᴰ = Γᴰ} ≡[ ap-Subᴰ ∃!ε ] σᴰ

      _[_]Tᴰ : Tyᴰ Δᴰ A → Subᴰ Γᴰ Δᴰ σ → Tyᴰ Γᴰ (A [ σ ]T)
      _[_]ᴰ : Tmᴰ Δᴰ i Aᴰ t → (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Tmᴰ Γᴰ i (Aᴰ [ σᴰ ]Tᴰ) (t [ σ ])
      _[_]#ᴰ : #∈ᴰ Δᴰ π → Subᴰ Γᴰ Δᴰ σ → #∈ᴰ Γᴰ (π [ σ ]#)
      [id]Tᴰ : Aᴰ [ idᴰ ]Tᴰ ≡[ ap-Tyᴰ [id]T ] Aᴰ
      [id]ᴰ : {tᴰ : Tmᴰ Δᴰ i Aᴰ t} → (tᴰ [ idᴰ ]ᴰ) ≡[ ap-Tmᴰ [id]T [id]Tᴰ [id] ] tᴰ
      [id]#ᴰ : πᴰ [ idᴰ ]#ᴰ ≡[ ap-#∈ᴰ [id]# ] πᴰ
      [∘]Tᴰ : Aᴰ [ σᴰ ∘ᴰ τᴰ ]Tᴰ ≡[ ap-Tyᴰ [∘]T ] (Aᴰ [ σᴰ ]Tᴰ) [ τᴰ ]Tᴰ
      [∘]ᴰ : {tᴰ : Tmᴰ Δᴰ i Aᴰ t} → (tᴰ [ σᴰ ∘ᴰ τᴰ ]ᴰ) ≡[ ap-Tmᴰ [∘]T [∘]Tᴰ [∘] ] ((tᴰ [ σᴰ ]ᴰ) [ τᴰ ]ᴰ)
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
      qᴰ : Tmᴰ (Γᴰ ▷ᴰ[ i ] Aᴰ) i (Aᴰ [ pᴰ ]Tᴰ) (q {Γ} {i} {A})
      _,,ᴰ_ : (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Tmᴰ Γᴰ i (Aᴰ [ σᴰ ]Tᴰ) t → Subᴰ Γᴰ (Δᴰ ▷ᴰ[ i ] Aᴰ) (σ ,, t)
      ,∘ᴰ : (σᴰ ,,ᴰ tᴰ) ∘ᴰ ρᴰ ≡[ ap-Subᴰ ,∘ ]
          (σᴰ ∘ᴰ ρᴰ) ,,ᴰ coe (ap-Tmᴰ (sym [∘]T) (symᴰ [∘]Tᴰ) refl) (tᴰ [ ρᴰ ]ᴰ)
      p,qᴰ : pᴰ {Γᴰ = Γᴰ} {i = i} {Aᴰ = Aᴰ} ,,ᴰ qᴰ ≡[ ap-Subᴰ p,q ] idᴰ
      p∘,ᴰ : pᴰ ∘ᴰ (σᴰ ,,ᴰ tᴰ) ≡[ ap-Subᴰ p∘, ] σᴰ
      q[,]ᴰ : {tᴰ : Tmᴰ Γᴰ i (Aᴰ [ σᴰ ]Tᴰ) t} → qᴰ [ σᴰ ,,ᴰ tᴰ ]ᴰ
          ≡[ ap-Tmᴰ (trans (sym [∘]T) (ap-[]T₀ p∘,))
                    (transᴰ (symᴰ [∘]Tᴰ) (ap-[]T₀ᴰ p∘, p∘,ᴰ))
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
                   (transᴰ (symᴰ [∘]Tᴰ)
                   (transᴰ (ap-[]T₀ᴰ p∘,# p∘,#ᴰ) [∘]Tᴰ)) refl)
                   (tᴰ [ σᴰ ⁺#ᴰ ]ᴰ))
      ↑↓ᴰ : ↑ᴰ (↓ᴰ tᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep ↑↓) ] tᴰ
      ↓↑ᴰ : ↓ᴰ (↑ᴰ tᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep ↓↑) ] tᴰ

    opaque
      unfolding ↓*  pz

      ↓*ᴰ : Tmᴰ Γᴰ i Aᴰ t → Tmᴰ Γᴰ z Aᴰ (↓* t)
      ↓*ᴰ {i = z} tᴰ = tᴰ
      ↓*ᴰ {i = ω} tᴰ = ↓ᴰ (tᴰ [ p#ᴰ ]ᴰ)

      pzᴰ : Subᴰ (Γᴰ ▷ᴰ[ i ] Aᴰ) (Γᴰ ▷ᴰ[ z ] Aᴰ) pz
      pzᴰ = pᴰ ,,ᴰ ↓*ᴰ qᴰ

      p,↓*qᴰ : (pᴰ {Γᴰ = Γᴰ} {i = _} {Aᴰ = Aᴰ} ,,ᴰ ↓*ᴰ {i = z} qᴰ) ≡[ ap-Subᴰ p,↓*q ] idᴰ
      p,↓*qᴰ = p,qᴰ

  module in-CwFwEᴰ-core (cᴰ : CwFwEᴰ-core) where
    open CwFwEᴰ-core cᴰ

    record Π-structureᴰ (ps : Π-structure) : Set where
      open Π-structure ps
      field
        Πᴰ : (i : Mode) → (Aᴰ : Tyᴰ Γᴰ A) → (Bᴰ : Tyᴰ (Γᴰ ▷ᴰ[ z ] Aᴰ) B) → Tyᴰ Γᴰ (Π i A B)
        Π[]ᴰ : (Πᴰ i Aᴰ Bᴰ) [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ Π[] ] Πᴰ i (Aᴰ [ σᴰ ]Tᴰ) (Bᴰ [ σᴰ ⁺ᴰ ]Tᴰ)

        lamᴰ : (tᴰ : Tmᴰ (Γᴰ ▷ᴰ[ i ] Aᴰ) ω (Bᴰ [ pzᴰ ]Tᴰ) t) → Tmᴰ Γᴰ ω (Πᴰ i Aᴰ Bᴰ) (lam t)
        -- Not including lam[]ᴰ because that would require proving the lemma pz∘⁺≡⁺∘pz
        -- in the displayed case. This doesn't even matter when we eliminate into Prop
        -- which is always the case in this repo. Either way it is possible to prove it.

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

  open CwFwE syn public
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

    Tm-injᶜ : Tm Γ i A ≡ Tm Γ' j A' → Γ ≡ Γ'
    Tm-injᵀ : (e : Tm Γ i A ≡ Tm Γ' j A') → A ≡[ ap-Tyᶜ (Tm-injᶜ e) ] A'
    Tm-injⁱ : (e : Tm Γ i A ≡ Tm Γ' j A') → i ≡ j

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

       ⟦coe⟧ᵗ : ∀ (p : Tm Γ i A ≡ Tm Γ' j A') →
        ⟦ coe p t ⟧ᵗ
          ≡ coe (ap-Tmᴰᶜ' (Tm-injᶜ p)  (Tm-injᵀ p) (ap-⟦⟧ᶜ (Tm-injᶜ p)) (Tm-injⁱ p) (ap-⟦⟧ᵀ (Tm-injᶜ p) (Tm-injᵀ p)) refl) ⟦ t ⟧ᵗ
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

-- Context eliminator
module CwFwE-elim-Con
  (open CwFwE-syntax)
  (P : Con → Set)
  (P∙ : P ∙)
  (P▷[z] : ∀ Γ A → P Γ → P (Γ ▷[ z ] A))
  (P▷[ω] : ∀ Γ A → P Γ → P (Γ ▷[ ω ] A))
  (P▷# : ∀ Γ → P Γ → P (Γ ▷#))
  where

  open CwFwEᴰ
  open CwFwEᴰ-sorts
  open in-CwFwEᴰ-sorts
  open CwFwEᴰ-core
  open in-CwFwEᴰ-core
  open Π-structureᴰ
  open U-structureᴰ

  nᴰ-sorts : CwFwEᴰ-sorts sorts
  nᴰ-sorts .Conᴰ Γ = P Γ
  nᴰ-sorts .Subᴰ _ _ _ = 𝟙
  nᴰ-sorts .Tyᴰ _ _ = 𝟙
  nᴰ-sorts .#∈ᴰ _ _ = 𝟙
  nᴰ-sorts .Tmᴰ _ _ _ _ = 𝟙
  nᴰ-sorts .#-propᴰ p₁ q₁ prf = refl

  nᴰ-core : CwFwEᴰ-core nᴰ-sorts core 
  nᴰ-core .idᴰ = tt
  nᴰ-core ._∘ᴰ_ = λ _ _ → tt
  nᴰ-core .assocᴰ = refl
  nᴰ-core .id∘ᴰ = refl
  nᴰ-core .∘idᴰ = refl
  nᴰ-core .∙ᴰ = P∙
  nᴰ-core .εᴰ = tt
  nᴰ-core .∃!εᴰ = refl
  nᴰ-core ._[_]Tᴰ = λ _ _ → tt
  nᴰ-core ._[_]ᴰ = λ _ σᴰ → tt
  nᴰ-core ._[_]#ᴰ = λ _ _ → tt
  nᴰ-core .[id]Tᴰ = refl
  nᴰ-core .[id]ᴰ = refl
  nᴰ-core .[id]#ᴰ = refl
  nᴰ-core .[∘]Tᴰ = refl
  nᴰ-core .[∘]ᴰ = refl
  nᴰ-core .[∘]#ᴰ = refl
  _▷ᴰ[_]_ nᴰ-core {Γ = Γ} {A = A} Γᴰ z _ = P▷[z] Γ A Γᴰ
  _▷ᴰ[_]_ nᴰ-core {Γ = Γ} {A = A} Γᴰ ω _ = P▷[ω] Γ A Γᴰ
  nᴰ-core .pᴰ = tt
  nᴰ-core .qᴰ = tt
  nᴰ-core ._,,ᴰ_ = λ σᴰ _ → tt
  nᴰ-core .,∘ᴰ = refl
  nᴰ-core .p,qᴰ = refl
  nᴰ-core .p∘,ᴰ = refl
  nᴰ-core .q[,]ᴰ = refl
  nᴰ-core ._▷#ᴰ {Γ = Γ} = P▷# Γ
  nᴰ-core .p#ᴰ = tt
  nᴰ-core .q#ᴰ = tt
  nᴰ-core ._,#ᴰ_ = λ _ _ → tt
  nᴰ-core .,#∘ᴰ = refl
  nᴰ-core .p,#qᴰ = refl
  nᴰ-core .p∘,#ᴰ = refl
  nᴰ-core .q[,#]ᴰ = refl
  nᴰ-core .↓ᴰ = λ _ → tt
  nᴰ-core .↑ᴰ = λ _ → tt
  nᴰ-core .↓[]ᴰ = refl
  nᴰ-core .↑↓ᴰ = refl
  nᴰ-core .↓↑ᴰ = refl

  nᴰ-Π-str : Π-structureᴰ nᴰ-sorts core nᴰ-core Π-str
  nᴰ-Π-str .Πᴰ = λ i Aᴰ Bᴰ → tt
  nᴰ-Π-str .Π[]ᴰ = refl
  nᴰ-Π-str .lamᴰ = λ tᴰ → tt
  nᴰ-Π-str .apᴰ = λ tᴰ → tt
  nᴰ-Π-str .Πβᴰ = refl
  nᴰ-Π-str .Πηᴰ = refl

  nᴰ-U-str : U-structureᴰ nᴰ-sorts core nᴰ-core U-str
  nᴰ-U-str .Uᴰ = tt
  nᴰ-U-str .U[]ᴰ = refl
  nᴰ-U-str .Elᴰ = λ tᴰ → tt
  nᴰ-U-str .El[]ᴰ = refl
  nᴰ-U-str .codeᴰ = λ Aᴰ → tt
  nᴰ-U-str .code[]ᴰ = refl
  nᴰ-U-str .El-codeᴰ = refl
  nᴰ-U-str .code-Elᴰ = refl

  nᴰ : CwFwEᴰ syn
  nᴰ .CwFwEᴰ.sortsᴰ = nᴰ-sorts
  nᴰ .CwFwEᴰ.coreᴰ = nᴰ-core
  nᴰ .CwFwEᴰ.Π-strᴰ = nᴰ-Π-str 
  nᴰ .CwFwEᴰ.U-strᴰ = nᴰ-U-str

  ⟦_⟧ : (Γ : Con) → P Γ
  ⟦_⟧ Γ = CwFwE-elim.⟦_⟧ᶜ nᴰ Γ


module CwFwE-uniform (m : CwFwE) (n : CwFwE) where

  open CwFwE n
  open CwFwE-sorts sorts
  open in-CwFwE-sorts sorts
  open CwFwE-core core
  open in-CwFwE-core core
  open Π-structure Π-str
  open U-structure U-str

  open CwFwEᴰ
  open CwFwEᴰ-sorts
  open in-CwFwEᴰ-sorts
  open CwFwEᴰ-core
  open in-CwFwEᴰ-core
  open Π-structureᴰ
  open U-structureᴰ

  nᴰ-sorts : CwFwEᴰ-sorts (m .CwFwE.sorts)
  nᴰ-sorts .Conᴰ _ = Con
  nᴰ-sorts .Subᴰ Γ Δ _ = Sub Γ Δ
  nᴰ-sorts .Tyᴰ Γ _ = Ty Γ
  nᴰ-sorts .#∈ᴰ Γ _ = #∈ Γ
  nᴰ-sorts .Tmᴰ Γ i A _ = Tm Γ i A
  nᴰ-sorts .#-propᴰ p₁ q₁ prf = #-prop (coe _ p₁) q₁

  nᴰ-core : CwFwEᴰ-core nᴰ-sorts (m .CwFwE.core)
  nᴰ-core .idᴰ = id
  nᴰ-core ._∘ᴰ_ = _∘_
  nᴰ-core .assocᴰ = dep assoc
  nᴰ-core .∘idᴰ = dep ∘id
  nᴰ-core .id∘ᴰ = dep id∘
  nᴰ-core .∙ᴰ = ∙
  nᴰ-core .εᴰ = ε
  nᴰ-core .∃!εᴰ = dep ∃!ε
  nᴰ-core ._[_]Tᴰ =  _[_]T
  nᴰ-core ._[_]ᴰ = _[_]
  nᴰ-core ._[_]#ᴰ = _[_]#
  nᴰ-core .[id]Tᴰ = dep [id]T
  nᴰ-core .[id]ᴰ = [id]
  nᴰ-core .[id]#ᴰ = dep [id]#
  nᴰ-core .[∘]Tᴰ = dep [∘]T
  nᴰ-core .[∘]ᴰ = [∘]
  nᴰ-core .[∘]#ᴰ = dep [∘]#
  nᴰ-core ._▷ᴰ[_]_ = _▷[_]_
  nᴰ-core .pᴰ = p
  nᴰ-core .qᴰ = q
  nᴰ-core ._,,ᴰ_ = _,,_
  nᴰ-core .,∘ᴰ = dep ,∘
  nᴰ-core .p,qᴰ = dep p,q
  nᴰ-core .p∘,ᴰ = dep p∘,
  nᴰ-core .q[,]ᴰ = q[,]
  nᴰ-core ._▷#ᴰ = _▷#
  nᴰ-core .p#ᴰ = p#
  nᴰ-core .q#ᴰ = q#
  nᴰ-core ._,#ᴰ_ = _,#_
  nᴰ-core .,#∘ᴰ = dep ,#∘
  nᴰ-core .p,#qᴰ = dep p,#q
  nᴰ-core .p∘,#ᴰ = dep p∘,#
  nᴰ-core .q[,#]ᴰ = dep q[,#]
  nᴰ-core .↓ᴰ = ↓
  nᴰ-core .↑ᴰ = ↑
  nᴰ-core .↓[]ᴰ = dep ↓[]
  nᴰ-core .↑↓ᴰ = dep ↑↓
  nᴰ-core .↓↑ᴰ = dep ↓↑

  opaque
    unfolding pzᴰ ↓*ᴰ

    nᴰ-Π-str : Π-structureᴰ nᴰ-sorts (m .CwFwE.core) nᴰ-core (m .CwFwE.Π-str)
    nᴰ-Π-str .Πᴰ = Π
    nᴰ-Π-str .Π[]ᴰ = dep Π[]
    nᴰ-Π-str .lamᴰ {i = z} =  lam {i = z} 
    nᴰ-Π-str .lamᴰ {i = ω} =  lam {i = ω} 
    nᴰ-Π-str .apᴰ {i = z} = ap
    nᴰ-Π-str .Πβᴰ {i = z} = dep Πβ
    nᴰ-Π-str .Πηᴰ {i = z} = dep Πη
    nᴰ-Π-str .apᴰ {i = ω} = ap
    nᴰ-Π-str .Πβᴰ {i = ω} = dep Πβ
    nᴰ-Π-str .Πηᴰ {i = ω} = dep Πη

  nᴰ-U-str : U-structureᴰ nᴰ-sorts (m .CwFwE.core) nᴰ-core (m .CwFwE.U-str)
  nᴰ-U-str .Uᴰ = U
  nᴰ-U-str .U[]ᴰ = dep U[]
  nᴰ-U-str .Elᴰ = El
  nᴰ-U-str .El[]ᴰ = dep El[]
  nᴰ-U-str .codeᴰ = code
  nᴰ-U-str .code[]ᴰ = code[]
  nᴰ-U-str .El-codeᴰ = dep El-code
  nᴰ-U-str .code-Elᴰ = dep code-El

  nᴰ : CwFwEᴰ m
  nᴰ .CwFwEᴰ.sortsᴰ = nᴰ-sorts
  nᴰ .CwFwEᴰ.coreᴰ = nᴰ-core
  nᴰ .CwFwEᴰ.Π-strᴰ = nᴰ-Π-str 
  nᴰ .CwFwEᴰ.U-strᴰ = nᴰ-U-str

