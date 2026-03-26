{-# OPTIONS --type-in-type --lossy-unification #-}
module Models.FO.Conservativity where

open import Utils
open import Theories.CwFwE
open import Theories.CwF
open import Data.Unit renaming (⊤ to 𝟙)
open import Data.Product
open import Mode

-- The ⌞_⌟ model
-- Interprets CwFwE using CwF

module _ (e : CwFwE)  where
  open CwFwE
  open CwFwE-sorts (e .sorts)
  open in-CwFwE-sorts (e .sorts)
  open CwFwE-core (e .core)
  open in-CwFwE-core (e .core)
  open Π-structure (e .Π-str)
  open U-structure (e .U-str)

  fg-sorts : CwFwE-sorts
  fg-sorts .CwFwE-sorts.Con = Con
  fg-sorts .CwFwE-sorts.Sub = Sub
  fg-sorts .CwFwE-sorts.Ty = Ty
  fg-sorts .CwFwE-sorts.#∈ Γ = 𝟙
  fg-sorts .CwFwE-sorts.Tm Γ i A = Tm Γ z A 
  fg-sorts .CwFwE-sorts.#-prop p₁ q₁ = refl

  fg-core : in-CwFwE-sorts.CwFwE-core fg-sorts
  fg-core .CwFwE-core.id = id
  fg-core .CwFwE-core._∘_ = _∘_
  fg-core .CwFwE-core.assoc = assoc
  fg-core .CwFwE-core.∘id = ∘id
  fg-core .CwFwE-core.id∘ = id∘
  fg-core .CwFwE-core.∙ = ∙
  fg-core .CwFwE-core.ε = ε
  fg-core .CwFwE-core.∃!ε = ∃!ε
  fg-core .CwFwE-core._[_]T = _[_]T
  fg-core .CwFwE-core._[_] = _[_]
  fg-core .CwFwE-core._[_]# = λ t σ → tt
  fg-core .CwFwE-core.[id]T = [id]T
  fg-core .CwFwE-core.[id] = [id]
  fg-core .CwFwE-core.[id]# = refl
  fg-core .CwFwE-core.[∘]T = [∘]T
  fg-core .CwFwE-core.[∘] = [∘]
  fg-core .CwFwE-core.[∘]# = refl
  (fg-core CwFwE-core.▷[ Γ ] i) A = Γ ▷[ z ] A
  fg-core .CwFwE-core.p = p
  fg-core .CwFwE-core.q = q
  fg-core .CwFwE-core._,,_ = _,,_
  fg-core .CwFwE-core.,∘ = ,∘
  fg-core .CwFwE-core.p,q = p,q
  fg-core .CwFwE-core.p∘, = p∘,
  fg-core .CwFwE-core.q[,] = q[,]
  (fg-core CwFwE-core.▷#) Γ = Γ
  fg-core .CwFwE-core.p# = id
  fg-core .CwFwE-core.q# = tt
  fg-core .CwFwE-core._,#_ = λ σ π → σ
  fg-core .CwFwE-core.,#∘ = refl
  fg-core .CwFwE-core.p,#q = refl
  fg-core .CwFwE-core.p∘,# = id∘
  fg-core .CwFwE-core.q[,#] = refl
  fg-core .CwFwE-core.↓ x = coe (ap-Tm [id]T) x
  fg-core .CwFwE-core.↑ x = x [ id ]
  fg-core .CwFwE-core.↓[] {t = t} = undep (splitr (splitr (ap-[] refl refl (dep (sym [id]T)) (dep (sym ∘id)) (splitl reflᴰ)))) 
  fg-core .CwFwE-core.↑↓ = undep (transᴰ {q = ap-Tm (sym [id]T)} [id] (splitl reflᴰ)) 
  fg-core .CwFwE-core.↓↑ = [id]

  -- -- This is annoying because of all the coercions so I will leave it out for now
  -- -- However, it definitely works because it works in the second-order model
  --
  -- opaque
  --   unfolding pz
  --   fg-Π : in-CwFwE-sorts.in-CwFwE-core.Π-structure fg-sorts fg-core
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Π i A B = Π i A B
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Π[] = Π[]
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam {i = z} f
  --     = ↓ (coe (ap-Tm (sym Π[])) (lam (coe (ap-Tm ( trans (sym [∘]T) ( trans (sym [∘]T) (trans (sym [∘]T)
  --     (trans (ap-[]T₀ (trans ( cong (_∘ _) p,q)
  --     (trans id∘ (cong (_ ∘_) (trans p∘,# (sym p,q)))))) [∘]T)))))
  --     ((↑ (f [ (p# ∘ p) ,, coe (ap-Tm (sym [∘]T)) q ])) [  id ,# (q# [ p ]#) ]))) )
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam {i = ω} f = {! !}
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam[] {z} = {! !}
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam[] {ω} = {!!}
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.ap = {! !}
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Πβ = {! !}
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Πη = {!!}

  fg-U : in-CwFwE-sorts.in-CwFwE-core.U-structure fg-sorts fg-core
  fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.U = U
  fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.U[] = U[]
  fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.El = El
  fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.El[] = El[]
  fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.code = code
  fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.code[] = code[]
  fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.El-code = El-code
  fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.code-El = code-El

  fg : CwFwE
  fg .sorts = fg-sorts
  fg .core = fg-core
  fg .Π-str = {!!}
  fg .U-str = fg-U

  fgᴰ : CwFwEᴰ e
  fgᴰ = CwFwE-uniform.nᴰ e fg 



-- The ⌜_⌝ model. Interprets CwF using the zeroed fragment of CwFwE
module _ (e : CwFwE)  where
  -- open CwFwE
  -- open CwFwE-sorts (e .sorts)
  -- open in-CwFwE-sorts (e .sorts)
  -- open CwFwE-core (e .core)
  -- open in-CwFwE-core (e .core)
  -- open Π-structure (e .Π-str)
  -- open U-structure (e .U-str)

  -- fg-sorts : CwFwE-sorts
  -- fg-sorts .CwFwE-sorts.Con = Con
  -- fg-sorts .CwFwE-sorts.Sub = Sub
  -- fg-sorts .CwFwE-sorts.Ty = Ty
  -- fg-sorts .CwFwE-sorts.#∈ Γ = 𝟙
  -- fg-sorts .CwFwE-sorts.Tm Γ i A = Tm Γ z A 
  -- fg-sorts .CwFwE-sorts.#-prop p₁ q₁ = refl

  -- fg-core : in-CwFwE-sorts.CwFwE-core fg-sorts
  -- fg-core .CwFwE-core.id = id
  -- fg-core .CwFwE-core._∘_ = _∘_
  -- fg-core .CwFwE-core.assoc = assoc
  -- fg-core .CwFwE-core.∘id = ∘id
  -- fg-core .CwFwE-core.id∘ = id∘
  -- fg-core .CwFwE-core.∙ = ∙
  -- fg-core .CwFwE-core.ε = ε
  -- fg-core .CwFwE-core.∃!ε = ∃!ε
  -- fg-core .CwFwE-core._[_]T = _[_]T
  -- fg-core .CwFwE-core._[_] = _[_]
  -- fg-core .CwFwE-core._[_]# = λ t σ → tt
  -- fg-core .CwFwE-core.[id]T = [id]T
  -- fg-core .CwFwE-core.[id] = [id]
  -- fg-core .CwFwE-core.[id]# = refl
  -- fg-core .CwFwE-core.[∘]T = [∘]T
  -- fg-core .CwFwE-core.[∘] = [∘]
  -- fg-core .CwFwE-core.[∘]# = refl
  -- (fg-core CwFwE-core.▷[ Γ ] i) A = Γ ▷[ z ] A
  -- fg-core .CwFwE-core.p = p
  -- fg-core .CwFwE-core.q = q
  -- fg-core .CwFwE-core._,,_ = _,,_
  -- fg-core .CwFwE-core.,∘ = ,∘
  -- fg-core .CwFwE-core.p,q = p,q
  -- fg-core .CwFwE-core.p∘, = p∘,
  -- fg-core .CwFwE-core.q[,] = q[,]
  -- (fg-core CwFwE-core.▷#) Γ = Γ
  -- fg-core .CwFwE-core.p# = id
  -- fg-core .CwFwE-core.q# = tt
  -- fg-core .CwFwE-core._,#_ = λ σ π → σ
  -- fg-core .CwFwE-core.,#∘ = refl
  -- fg-core .CwFwE-core.p,#q = refl
  -- fg-core .CwFwE-core.p∘,# = id∘
  -- fg-core .CwFwE-core.q[,#] = refl
  -- fg-core .CwFwE-core.↓ x = coe (ap-Tm [id]T) x
  -- fg-core .CwFwE-core.↑ x = x [ id ]
  -- fg-core .CwFwE-core.↓[] {t = t} = undep (splitr (splitr (ap-[] refl refl (dep (sym [id]T)) (dep (sym ∘id)) (splitl reflᴰ)))) 
  -- fg-core .CwFwE-core.↑↓ = undep (transᴰ {q = ap-Tm (sym [id]T)} [id] (splitl reflᴰ)) 
  -- fg-core .CwFwE-core.↓↑ = [id]

  -- -- This is annoying because of all the coercions so I will leave it out for now
  -- -- However, it definitely works because it works in the second-order model
  --
  -- opaque
  --   unfolding pz
  --   fg-Π : in-CwFwE-sorts.in-CwFwE-core.Π-structure fg-sorts fg-core
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Π i A B = Π i A B
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Π[] = Π[]
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam {i = z} f
  --     = ↓ (coe (ap-Tm (sym Π[])) (lam (coe (ap-Tm ( trans (sym [∘]T) ( trans (sym [∘]T) (trans (sym [∘]T)
  --     (trans (ap-[]T₀ (trans ( cong (_∘ _) p,q)
  --     (trans id∘ (cong (_ ∘_) (trans p∘,# (sym p,q)))))) [∘]T)))))
  --     ((↑ (f [ (p# ∘ p) ,, coe (ap-Tm (sym [∘]T)) q ])) [  id ,# (q# [ p ]#) ]))) )
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam {i = ω} f = {! !}
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam[] {z} = {! !}
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam[] {ω} = {!!}
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.ap = {! !}
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Πβ = {! !}
  --   fg-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Πη = {!!}

  -- fg-U : in-CwFwE-sorts.in-CwFwE-core.U-structure fg-sorts fg-core
  -- fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.U = U
  -- fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.U[] = U[]
  -- fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.El = El
  -- fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.El[] = El[]
  -- fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.code = code
  -- fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.code[] = code[]
  -- fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.El-code = El-code
  -- fg-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.code-El = code-El

  -- fg : CwFwE
  -- fg .sorts = fg-sorts
  -- fg .core = fg-core
  -- fg .Π-str = {!!}
  -- fg .U-str = fg-U

  -- fgᴰ : CwFwEᴰ e
  -- fgᴰ = CwFwE-uniform.nᴰ e fg 


-- Conservativity:
--
-- There is a surjective (ie with an inverse) map Tm z ⌜Γ⌝ ⌜A⌝ → Tm Γ A
