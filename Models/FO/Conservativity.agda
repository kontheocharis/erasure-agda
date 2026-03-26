{-# OPTIONS --type-in-type --lossy-unification #-}
module Models.FO.Conservativity where

open import Utils
open import Theories.CwFwE
open import Theories.CwF
open import Data.Unit renaming (⊤ to 𝟙)
open import Data.Product
open import Mode

-- ⌜⌝ : CwFwE → CwF
module _ (e : CwFwE)  where
  open CwFwE
  open CwFwE-sorts (e .sorts)
  open in-CwFwE-sorts (e .sorts)
  open CwFwE-core (e .core)
  open in-CwFwE-core (e .core)
  open Π-structure (e .Π-str)
  open U-structure (e .U-str)
  open CwF

  ⌜⌝-sorts : CwF-sorts
  ⌜⌝-sorts .CwF-sorts.Con = Con
  ⌜⌝-sorts .CwF-sorts.Sub = Sub
  ⌜⌝-sorts .CwF-sorts.Ty = Ty
  ⌜⌝-sorts .CwF-sorts.Tm Γ A = Tm Γ z A

  open in-CwF-sorts ⌜⌝-sorts

  ⌜⌝-core : CwF-core
  ⌜⌝-core .CwF-core.id = id
  ⌜⌝-core .CwF-core._∘_ = _∘_
  ⌜⌝-core .CwF-core.assoc = assoc
  ⌜⌝-core .CwF-core.id∘ = id∘
  ⌜⌝-core .CwF-core.∘id = ∘id
  ⌜⌝-core .CwF-core.∙ = ∙
  ⌜⌝-core .CwF-core.ε = ε
  ⌜⌝-core .CwF-core.∃!ε = ∃!ε
  ⌜⌝-core .CwF-core._[_]T = _[_]T
  ⌜⌝-core .CwF-core._[_] = _[_]
  ⌜⌝-core .CwF-core.[id]T = [id]T
  ⌜⌝-core .CwF-core.[id] = [id]
  ⌜⌝-core .CwF-core.[∘]T = [∘]T
  ⌜⌝-core .CwF-core.[∘] = [∘]
  ⌜⌝-core .CwF-core._▷_ = _▷[ z ]_
  ⌜⌝-core .CwF-core.p = p
  ⌜⌝-core .CwF-core.q = q
  ⌜⌝-core .CwF-core._,,_ = _,,_
  ⌜⌝-core .CwF-core.,∘ = ,∘
  ⌜⌝-core .CwF-core.p,q = p,q
  ⌜⌝-core .CwF-core.p∘, = p∘,
  ⌜⌝-core .CwF-core.q[,] = q[,]

  open in-CwF-core ⌜⌝-core

  ⌜⌝-U : in-CwF-sorts.in-CwF-core.U-structure ⌜⌝-sorts ⌜⌝-core
  ⌜⌝-U .in-CwF-sorts.in-CwF-core.U-structure.U = U
  ⌜⌝-U .in-CwF-sorts.in-CwF-core.U-structure.U[] = U[]
  ⌜⌝-U .in-CwF-sorts.in-CwF-core.U-structure.El = El
  ⌜⌝-U .in-CwF-sorts.in-CwF-core.U-structure.El[] = El[]
  ⌜⌝-U .in-CwF-sorts.in-CwF-core.U-structure.code = code
  ⌜⌝-U .in-CwF-sorts.in-CwF-core.U-structure.code[] = code[]
  ⌜⌝-U .in-CwF-sorts.in-CwF-core.U-structure.El-code = El-code
  ⌜⌝-U .in-CwF-sorts.in-CwF-core.U-structure.code-El = code-El

  ⌜⌝ : CwF
  ⌜⌝ .CwF.sorts = ⌜⌝-sorts
  ⌜⌝ .CwF.core = ⌜⌝-core
  ⌜⌝ .CwF.Π-str = {!!}
  ⌜⌝ .CwF.U-str = ⌜⌝-U

-- ⌞⌟ : CwF → CwFwE
module ⌞⌟-mod (m : CwF) where
  open CwF-sorts (CwF.sorts m)
  open in-CwF-sorts (CwF.sorts m)
  open in-CwF-sorts.CwF-core (CwF.core m)
  open in-CwF-sorts.in-CwF-core (CwF.sorts m) (CwF.core m)
  open in-CwF-sorts.in-CwF-core.Π-structure (CwF.Π-str m)
  open in-CwF-sorts.in-CwF-core.U-structure (CwF.U-str m)
  open CwFwE

  ⌞⌟-sorts : CwFwE-sorts
  ⌞⌟-sorts .CwFwE-sorts.Con = Con
  ⌞⌟-sorts .CwFwE-sorts.Sub = Sub
  ⌞⌟-sorts .CwFwE-sorts.Ty = Ty
  ⌞⌟-sorts .CwFwE-sorts.#∈ _ = 𝟙
  ⌞⌟-sorts .CwFwE-sorts.Tm Γ i A = Tm Γ A
  ⌞⌟-sorts .CwFwE-sorts.#-prop _ _ = refl

  open in-CwFwE-sorts ⌞⌟-sorts using (CwFwE-core)
  ⌞⌟-core : CwFwE-core
  ⌞⌟-core .CwFwE-core.id = id
  ⌞⌟-core .CwFwE-core._∘_ = _∘_
  ⌞⌟-core .CwFwE-core.assoc = assoc
  ⌞⌟-core .CwFwE-core.∘id = ∘id
  ⌞⌟-core .CwFwE-core.id∘ = id∘
  ⌞⌟-core .CwFwE-core.∙ = ∙
  ⌞⌟-core .CwFwE-core.ε = ε
  ⌞⌟-core .CwFwE-core.∃!ε = ∃!ε
  ⌞⌟-core .CwFwE-core._[_]T = _[_]T
  ⌞⌟-core .CwFwE-core._[_] = _[_]
  ⌞⌟-core .CwFwE-core._[_]# = λ _ _ → tt
  ⌞⌟-core .CwFwE-core.[id]T = [id]T
  ⌞⌟-core .CwFwE-core.[id] = [id]
  ⌞⌟-core .CwFwE-core.[id]# = refl
  ⌞⌟-core .CwFwE-core.[∘]T = [∘]T
  ⌞⌟-core .CwFwE-core.[∘] = [∘]
  ⌞⌟-core .CwFwE-core.[∘]# = refl
  (⌞⌟-core CwFwE-core.▷[ Γ ] i) A = Γ ▷ A
  ⌞⌟-core .CwFwE-core.p = p
  ⌞⌟-core .CwFwE-core.q = q
  ⌞⌟-core .CwFwE-core._,,_ = _,,_
  ⌞⌟-core .CwFwE-core.,∘ = ,∘
  ⌞⌟-core .CwFwE-core.p,q = p,q
  ⌞⌟-core .CwFwE-core.p∘, = p∘,
  ⌞⌟-core .CwFwE-core.q[,] = q[,]
  (⌞⌟-core CwFwE-core.▷#) Γ = Γ
  ⌞⌟-core .CwFwE-core.p# = id
  ⌞⌟-core .CwFwE-core.q# = tt
  ⌞⌟-core .CwFwE-core._,#_ = λ σ _ → σ
  ⌞⌟-core .CwFwE-core.,#∘ = refl
  ⌞⌟-core .CwFwE-core.p,#q = refl
  ⌞⌟-core .CwFwE-core.p∘,# = id∘
  ⌞⌟-core .CwFwE-core.q[,#] = refl
  ⌞⌟-core .CwFwE-core.↓ x = coe (ap-Tm [id]T) x
  ⌞⌟-core .CwFwE-core.↑ x = x [ id ]
  ⌞⌟-core .CwFwE-core.↓[] {t = t} = undep (splitr (splitr (ap-[] refl refl (dep (sym [id]T)) (dep (sym ∘id)) (splitl reflᴰ))))
  ⌞⌟-core .CwFwE-core.↑↓ = undep (transᴰ {q = ap-Tm (sym [id]T)} [id] (splitl reflᴰ))
  ⌞⌟-core .CwFwE-core.↓↑ = [id]

  ⌞⌟-U : in-CwFwE-sorts.in-CwFwE-core.U-structure ⌞⌟-sorts ⌞⌟-core
  ⌞⌟-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.U = U
  ⌞⌟-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.U[] = U[]
  ⌞⌟-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.El = El
  ⌞⌟-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.El[] = El[]
  ⌞⌟-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.code = code
  ⌞⌟-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.code[] = code[]
  ⌞⌟-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.El-code = El-code
  ⌞⌟-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.code-El = code-El

  opaque
    unfolding CwFwE-core.pz CwFwE-core.↓*
    pz≡id : ∀ {i} → CwFwE-core.pz ⌞⌟-core {Γ} {i} {A} ≡ id
    pz≡id {i = z} = p,q
    pz≡id {i = ω} = trans (cong (p ,,_) (undep (dep [id]))) p,q

    B[pz]≡B : ∀ {i} → B [ CwFwE-core.pz ⌞⌟-core {Γ} {i} {A} ]T ≡ B
    B[pz]≡B = trans (ap-[]T₀ pz≡id) [id]T

  ⌞⌟-Π : in-CwFwE-sorts.in-CwFwE-core.Π-structure ⌞⌟-sorts ⌞⌟-core
  ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Π i A B = Π A B
  ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Π[] = Π[]
  ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam {i = i} f = lam (coe (ap-Tm (B[pz]≡B {i = i})) f)
  ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam[] = {!    !}
  ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.ap f = coe (ap-Tm B[pz]≡B) {!!}
  ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Πβ = {!!}
  ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Πη = {!!}

  ⌞⌟ : CwFwE
  ⌞⌟ .sorts = ⌞⌟-sorts
  ⌞⌟ .core = ⌞⌟-core
  ⌞⌟ .Π-str = ⌞⌟-Π
  ⌞⌟ .U-str = ⌞⌟-U

-- Conservativity
-- ⌞⌜ t ⌝⌟ = t

module Conservativity where
  module C = CwF-syntax
  module E = CwFwE-syntax
  open CwF-syntax renaming (syn to cwf)
  open CwFwE-syntax renaming (syn to cwfwe) hiding (Con; Sub; Ty)

  module ⌜_⌝-elim = CwF-syntax.CwF-elim (CwF-uniform.nᴰ cwf (⌜⌝ cwfwe))
  ⌜_⌝ᶜ = ⌜_⌝-elim.⟦_⟧ᶜ
  ⌜_⌝ᵀ = ⌜_⌝-elim.⟦_⟧ᵀ
  ⌜_⌝ˢ = ⌜_⌝-elim.⟦_⟧ˢ
  ⌜_⌝ᵗ = ⌜_⌝-elim.⟦_⟧ᵗ

  module ⌞_⌟-elim = CwFwE-syntax.CwFwE-elim (CwFwE-uniform.nᴰ cwfwe (⌞⌟-mod.⌞⌟ cwf))
  ⌞_⌟ᶜ = ⌞_⌟-elim.⟦_⟧ᶜ
  ⌞_⌟ᵀ = ⌞_⌟-elim.⟦_⟧ᵀ
  ⌞_⌟ˢ = ⌞_⌟-elim.⟦_⟧ˢ
  ⌞_⌟ᵗ = ⌞_⌟-elim.⟦_⟧ᵗ

  open CwFᴰ
  open CwFᴰ-sorts
  open in-CwFᴰ-sorts
  open in-CwFᴰ-core

  private
    co-sorts : CwFᴰ-sorts (CwF.sorts cwf)
    co-sorts .Conᴰ Γ =
      (⌞ ⌜ Γ ⌝ᶜ ⌟ᶜ ≡ Γ) true
    co-sorts .Subᴰ {Γ} {Δ} Γᴰ Δᴰ σ =
      (⌞ ⌜ σ ⌝ˢ ⌟ˢ ≡[ C.ap-Subᶜ (Γᴰ .witness) (Δᴰ .witness) ] σ) true
    co-sorts .Tyᴰ {Γ} Γᴰ A =
      (⌞ ⌜ A ⌝ᵀ ⌟ᵀ ≡[ C.ap-Tyᶜ (Γᴰ .witness) ] A) true
    co-sorts .Tmᴰ {Γ} {A} Γᴰ Aᴰ t =
      (⌞ ⌜ t ⌝ᵗ ⌟ᵗ ≡[ C.ap-Tmᶜ (Γᴰ .witness) (Aᴰ .witness) ] t) true

    co-core : in-CwFᴰ-sorts.CwFᴰ-core co-sorts (CwF.core cwf)
    co-core .CwFᴰ-core.idᴰ {Γᴰ = Γᴰ} .witness = (C.ap-id (Γᴰ .witness))
    co-core .CwFᴰ-core._∘ᴰ_ {Δᴰ = Δᴰ} {Θᴰ = Θᴰ} {Γᴰ = Γᴰ} σᴰ τᴰ =
      by (C.ap-∘ (Δᴰ .witness) (Θᴰ .witness) (Γᴰ .witness) (σᴰ .witness) (τᴰ .witness))
    co-core .CwFᴰ-core.assocᴰ = refl
    co-core .CwFᴰ-core.id∘ᴰ = refl
    co-core .CwFᴰ-core.∘idᴰ = refl
    co-core .CwFᴰ-core.∙ᴰ = by refl
    co-core .CwFᴰ-core.εᴰ {Γᴰ = Γᴰ} = by (C.ap-ε (Γᴰ .witness))
    co-core .CwFᴰ-core.∃!εᴰ = refl
    co-core .CwFᴰ-core._[_]Tᴰ {Δᴰ = Δᴰ} {Γᴰ = Γᴰ} Aᴰ σᴰ =
      by (C.ap-[]T (Γᴰ .witness) (Δᴰ .witness) (Aᴰ .witness) (σᴰ .witness))
    co-core .CwFᴰ-core._[_]ᴰ {Δᴰ = Δᴰ} {Aᴰ = Aᴰ} {Γᴰ = Γᴰ} tᴰ σᴰ =
      by (C.ap-[] (Γᴰ .witness) (Δᴰ .witness) (Aᴰ .witness) (σᴰ .witness) (tᴰ .witness))
    co-core .CwFᴰ-core.[id]Tᴰ = refl
    co-core .CwFᴰ-core.[id]ᴰ = refl
    co-core .CwFᴰ-core.[∘]Tᴰ = refl
    co-core .CwFᴰ-core.[∘]ᴰ = refl
    co-core .CwFᴰ-core._▷ᴰ_ Γᴰ Aᴰ = by (C.ap-▷ (Γᴰ .witness) (Aᴰ .witness))
    co-core .CwFᴰ-core.pᴰ {Γᴰ = Γᴰ} {Aᴰ = Aᴰ} = by (C.ap-p (Γᴰ .witness) (Aᴰ .witness))
    co-core .CwFᴰ-core.qᴰ {Γᴰ = Γᴰ} {Aᴰ = Aᴰ} = by (C.ap-q (Γᴰ .witness) (Aᴰ .witness))
    co-core .CwFᴰ-core._,,ᴰ_ {Γᴰ = Γᴰ} {Δᴰ = Δᴰ} {Aᴰ = Aᴰ} σᴰ tᴰ =
      by (C.ap-,, (Γᴰ .witness) (Δᴰ .witness) (σᴰ .witness) (Aᴰ .witness) (tᴰ .witness))
    co-core .CwFᴰ-core.,∘ᴰ = refl
    co-core .CwFᴰ-core.p,qᴰ = refl
    co-core .CwFᴰ-core.p∘,ᴰ = refl
    co-core .CwFᴰ-core.q[,]ᴰ = refl

    co-Π : Π-structureᴰ co-sorts (CwF.core cwf) co-core (CwF.Π-str cwf)
    co-Π .Π-structureᴰ.Πᴰ Aᴰ Bᴰ = {!!}
    co-Π .Π-structureᴰ.Π[]ᴰ = {!!}
    co-Π .Π-structureᴰ.lamᴰ tᴰ = {!!}
    co-Π .Π-structureᴰ.lamᴰ[] = {!!}
    co-Π .Π-structureᴰ.apᴰ tᴰ = {!!}
    co-Π .Π-structureᴰ.Πβᴰ = {!!}
    co-Π .Π-structureᴰ.Πηᴰ = {!!}

    co-U : U-structureᴰ co-sorts (CwF.core cwf) co-core (CwF.U-str cwf)
    co-U .U-structureᴰ.Uᴰ {Γᴰ = Γᴰ} = by (C.ap-U (Γᴰ .witness))
    co-U .U-structureᴰ.U[]ᴰ = refl
    co-U .U-structureᴰ.Elᴰ {Γᴰ = Γᴰ} tᴰ = by (C.ap-El (Γᴰ .witness) (tᴰ .witness))
    co-U .U-structureᴰ.El[]ᴰ = refl
    co-U .U-structureᴰ.codeᴰ {Γᴰ = Γᴰ} Aᴰ = by (C.ap-code (Γᴰ .witness) (Aᴰ .witness))
    co-U .U-structureᴰ.code[]ᴰ = refl
    co-U .U-structureᴰ.El-codeᴰ = refl
    co-U .U-structureᴰ.code-Elᴰ = refl

    co : CwFᴰ cwf
    co .CwFᴰ.sortsᴰ = co-sorts
    co .CwFᴰ.coreᴰ = co-core
    co .CwFᴰ.Π-strᴰ = co-Π
    co .CwFᴰ.U-strᴰ = co-U

  module CO = CwF-syntax.CwF-elim co

  ⌞⌜⌝⌟-Con : (Γ : Con) → ⌞ ⌜ Γ ⌝ᶜ ⌟ᶜ ≡ Γ
  ⌞⌜⌝⌟-Con Γ = CO.⟦ Γ ⟧ᶜ .witness

  ⌞⌜⌝⌟-Ty : (Γ : Con) (A : Ty Γ) → ⌞ ⌜ A ⌝ᵀ ⌟ᵀ ≡[ cong Ty (⌞⌜⌝⌟-Con Γ) ] A
  ⌞⌜⌝⌟-Ty Γ A = CO.⟦ A ⟧ᵀ .witness

  ⌞⌜⌝⌟-Tm : (Γ : Con) (A : Ty Γ) (t : C.Tm Γ A)
    → ⌞ ⌜ t ⌝ᵗ ⌟ᵗ ≡[ C.ap-Tmᶜ (⌞⌜⌝⌟-Con Γ) (⌞⌜⌝⌟-Ty Γ A) ] t
  ⌞⌜⌝⌟-Tm Γ A t = CO.⟦ t ⟧ᵗ .witness

  -- Erased conservativity
  erased-conservativity : (Γ : Con) (A : Ty Γ)
    → E.Tm ⌜ Γ ⌝ᶜ z ⌜ A ⌝ᵀ → C.Tm Γ A
  erased-conservativity Γ A u =
    coe (C.ap-Tmᶜ (⌞⌜⌝⌟-Con Γ) (⌞⌜⌝⌟-Ty Γ A)) ⌞ u ⌟ᵗ

  erased-section : (Γ : Con) (A : Ty Γ) (t : C.Tm Γ A)
    → erased-conservativity Γ A ⌜ t ⌝ᵗ ≡ t
  erased-section Γ A t = ⌞⌜⌝⌟-Tm Γ A t

  -- Runtime conservativity
  module _ (Γ : Con) (A : Ty Γ) where
    module zero = CwFwE-syntax.CwFwE-elim
      (CwFwE-uniform.nᴰ cwfwe (⌞⌟-mod.⌞⌟ (⌜⌝ cwfwe)))

    runtime-conservativity :
        (Γ' : E.Con) (A' : E.Ty Γ')
      → (pΓ : zero.⟦ Γ' ⟧ᶜ ≡ ⌜ Γ ⌝ᶜ)
      → (pA : zero.⟦ A' ⟧ᵀ ≡[ E.ap-Tyᶜ pΓ ] ⌜ A ⌝ᵀ)
      → E.Tm Γ' ω A' → C.Tm Γ A
    runtime-conservativity Γ' A' pΓ pA u =
      erased-conservativity Γ A
        (coe (E.ap-Tmᶜ' pΓ refl pA) (zero.⟦ u ⟧ᵗ))
