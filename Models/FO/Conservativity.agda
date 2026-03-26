{-# OPTIONS --type-in-type --lossy-unification #-}
module Models.FO.Conservativity where

open import Utils
open import Theories.CwFwE
open import Theories.CwF
open import Data.Unit renaming (⊤ to 𝟙)
open import Data.Product
open import Mode

-- The ⌞⌟ model
-- Interprets CwFwE using CwF

module _ (e : CwFwE)  where
  open CwFwE
  open CwFwE-sorts (e .sorts)
  open in-CwFwE-sorts (e .sorts)
  open CwFwE-core (e .core)
  open in-CwFwE-core (e .core)
  open Π-structure (e .Π-str)
  open U-structure (e .U-str)

  ⌞⌟-sorts : CwFwE-sorts
  ⌞⌟-sorts .CwFwE-sorts.Con = Con
  ⌞⌟-sorts .CwFwE-sorts.Sub = Sub
  ⌞⌟-sorts .CwFwE-sorts.Ty = Ty
  ⌞⌟-sorts .CwFwE-sorts.#∈ Γ = 𝟙
  ⌞⌟-sorts .CwFwE-sorts.Tm Γ i A = Tm Γ z A 
  ⌞⌟-sorts .CwFwE-sorts.#-prop p₁ q₁ = refl

  ⌞⌟-core : in-CwFwE-sorts.CwFwE-core ⌞⌟-sorts
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
  ⌞⌟-core .CwFwE-core._[_]# = λ t σ → tt
  ⌞⌟-core .CwFwE-core.[id]T = [id]T
  ⌞⌟-core .CwFwE-core.[id] = [id]
  ⌞⌟-core .CwFwE-core.[id]# = refl
  ⌞⌟-core .CwFwE-core.[∘]T = [∘]T
  ⌞⌟-core .CwFwE-core.[∘] = [∘]
  ⌞⌟-core .CwFwE-core.[∘]# = refl
  (⌞⌟-core CwFwE-core.▷[ Γ ] i) A = Γ ▷[ z ] A
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
  ⌞⌟-core .CwFwE-core._,#_ = λ σ π → σ
  ⌞⌟-core .CwFwE-core.,#∘ = refl
  ⌞⌟-core .CwFwE-core.p,#q = refl
  ⌞⌟-core .CwFwE-core.p∘,# = id∘
  ⌞⌟-core .CwFwE-core.q[,#] = refl
  ⌞⌟-core .CwFwE-core.↓ x = coe (ap-Tm [id]T) x
  ⌞⌟-core .CwFwE-core.↑ x = x [ id ]
  ⌞⌟-core .CwFwE-core.↓[] {t = t} = undep (splitr (splitr (ap-[] refl refl (dep (sym [id]T)) (dep (sym ∘id)) (splitl reflᴰ)))) 
  ⌞⌟-core .CwFwE-core.↑↓ = undep (transᴰ {q = ap-Tm (sym [id]T)} [id] (splitl reflᴰ)) 
  ⌞⌟-core .CwFwE-core.↓↑ = [id]

  -- -- This is annoying because of all the coercions so I will leave it out for now
  -- -- However, it definitely works because it works in the second-order model
  --
  -- opaque
  --   unfolding pz
  --   ⌞⌟-Π : in-CwFwE-sorts.in-CwFwE-core.Π-structure ⌞⌟-sorts ⌞⌟-core
  --   ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Π i A B = Π i A B
  --   ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Π[] = Π[]
  --   ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam {i = z} f
  --     = ↓ (coe (ap-Tm (sym Π[])) (lam (coe (ap-Tm ( trans (sym [∘]T) ( trans (sym [∘]T) (trans (sym [∘]T)
  --     (trans (ap-[]T₀ (trans ( cong (_∘ _) p,q)
  --     (trans id∘ (cong (_ ∘_) (trans p∘,# (sym p,q)))))) [∘]T)))))
  --     ((↑ (f [ (p# ∘ p) ,, coe (ap-Tm (sym [∘]T)) q ])) [  id ,# (q# [ p ]#) ]))) )
  --   ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam {i = ω} f = {! !}
  --   ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam[] {z} = {! !}
  --   ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam[] {ω} = {!!}
  --   ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.ap = {! !}
  --   ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Πβ = {! !}
  --   ⌞⌟-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Πη = {!!}

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

  ⌞⌟ᴰ : CwFwEᴰ e
  ⌞⌟ᴰ = CwFwE-uniform.nᴰ e ⌞⌟

  ⌜⌝ᴰ : CwFwEᴰ ⌞⌟
  ⌜⌝ᴰ = CwFwE-uniform.nᴰ ⌞⌟ e



-- The ⌜⌝ model. Interprets CwF using the zeroed fragment of CwFwE
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

-- Conservativity:
