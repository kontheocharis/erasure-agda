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
  ⌞⌟-core .CwFwE-core.↓[] = {!!}
  ⌞⌟-core .CwFwE-core.↑↓ = {!!}
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

  ⌞⌟ : CwFwE
  ⌞⌟ .sorts = ⌞⌟-sorts
  ⌞⌟ .core = ⌞⌟-core
  ⌞⌟ .Π-str = {!!}
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

  -- TODO
  postulate
    ⌞⌜⌝⌟-Con : (Γ : Con) → ⌞ ⌜ Γ ⌝ᶜ ⌟ᶜ ≡ Γ
    ⌞⌜⌝⌟-Ty  : (Γ : Con) (A : Ty Γ)
      → ⌞ ⌜ A ⌝ᵀ ⌟ᵀ ≡[ cong Ty (⌞⌜⌝⌟-Con Γ) ] A
    ⌞⌜⌝⌟-Tm  : (Γ : Con) (A : Ty Γ) (t : C.Tm Γ A)
      → ⌞ ⌜ t ⌝ᵗ ⌟ᵗ ≡[ C.ap-Tmᶜ (⌞⌜⌝⌟-Con Γ) (⌞⌜⌝⌟-Ty Γ A) ] t

  -- Erased conservativity
  erased-conservativity : (Γ : Con) (A : Ty Γ)
    → E.Tm ⌜ Γ ⌝ᶜ z ⌜ A ⌝ᵀ → C.Tm Γ A
  erased-conservativity Γ A u =
    coe (C.ap-Tmᶜ (⌞⌜⌝⌟-Con Γ) (⌞⌜⌝⌟-Ty Γ A)) ⌞ u ⌟ᵗ

  erased-section : (Γ : Con) (A : Ty Γ) (t : C.Tm Γ A)
    → erased-conservativity Γ A ⌜ t ⌝ᵗ ≡ t
  erased-section = ⌞⌜⌝⌟-Tm

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
