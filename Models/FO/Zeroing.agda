module Models.FO.Zeroing where

open import Utils
open import Theories.CwFwE
open import Theories.QCwF
open import Data.Unit renaming (⊤ to 𝟙)
open import Data.Product
open import Mode


module _ (e-sorts : CwFwE-sorts) (e-core : in-CwFwE-sorts.CwFwE-core e-sorts) where
  open CwFwE-sorts e-sorts
  open in-CwFwE-sorts.CwFwE-core e-core
  open in-CwFwE-sorts.in-CwFwE-core e-sorts e-core

  ze-sorts : CwFwE-sorts
  ze-sorts .CwFwE-sorts.Con = Con
  ze-sorts .CwFwE-sorts.Sub = Sub
  ze-sorts .CwFwE-sorts.Ty = Ty
  ze-sorts .CwFwE-sorts.#∈ Γ = 𝟙
  ze-sorts .CwFwE-sorts.Tm Γ i A = Tm Γ z A 

  ze-core : in-CwFwE-sorts.CwFwE-core ze-sorts
  ze-core .in-CwFwE-sorts.CwFwE-core.id = id
  ze-core .in-CwFwE-sorts.CwFwE-core._∘_ = _∘_
  ze-core .in-CwFwE-sorts.CwFwE-core.assoc = assoc
  ze-core .in-CwFwE-sorts.CwFwE-core.∘id = ∘id
  ze-core .in-CwFwE-sorts.CwFwE-core.id∘ = id∘
  ze-core .in-CwFwE-sorts.CwFwE-core.∙ = ∙
  ze-core .in-CwFwE-sorts.CwFwE-core.ε = ε
  ze-core .in-CwFwE-sorts.CwFwE-core.∃!ε = ∃!ε
  ze-core .in-CwFwE-sorts.CwFwE-core._[_]T = _[_]T
  ze-core .in-CwFwE-sorts.CwFwE-core._[_] = _[_]
  ze-core .in-CwFwE-sorts.CwFwE-core._[_]# = λ t σ → tt
  ze-core .in-CwFwE-sorts.CwFwE-core.[id]T = [id]T
  ze-core .in-CwFwE-sorts.CwFwE-core.[id] = [id]
  ze-core .in-CwFwE-sorts.CwFwE-core.[id]# = refl
  ze-core .in-CwFwE-sorts.CwFwE-core.[∘]T = [∘]T
  ze-core .in-CwFwE-sorts.CwFwE-core.[∘] = [∘]
  ze-core .in-CwFwE-sorts.CwFwE-core.[∘]# = refl
  (ze-core in-CwFwE-sorts.CwFwE-core.▷[ Γ ] i) A = Γ ▷[ z ] A
  ze-core .in-CwFwE-sorts.CwFwE-core.p = p
  ze-core .in-CwFwE-sorts.CwFwE-core.q = q
  ze-core .in-CwFwE-sorts.CwFwE-core._,,_ = _,,_
  ze-core .in-CwFwE-sorts.CwFwE-core.,∘ = ,∘
  ze-core .in-CwFwE-sorts.CwFwE-core.p,q = p,q
  ze-core .in-CwFwE-sorts.CwFwE-core.p∘, = p∘,
  ze-core .in-CwFwE-sorts.CwFwE-core.q[,] = q[,]
  (ze-core in-CwFwE-sorts.CwFwE-core.▷#) Γ = Γ
  ze-core .in-CwFwE-sorts.CwFwE-core.p# = id
  ze-core .in-CwFwE-sorts.CwFwE-core.q# = tt
  ze-core .in-CwFwE-sorts.CwFwE-core._,#_ = λ σ π → σ
  ze-core .in-CwFwE-sorts.CwFwE-core.,#∘ = refl
  ze-core .in-CwFwE-sorts.CwFwE-core.p,#q = refl
  ze-core .in-CwFwE-sorts.CwFwE-core.p∘,# = ∘id
  ze-core .in-CwFwE-sorts.CwFwE-core.q[,#] = refl
  ze-core .in-CwFwE-sorts.CwFwE-core.↓ x = coe (cong (Tm _ _) [id]T) x
  ze-core .in-CwFwE-sorts.CwFwE-core.↑ x = x [ id ]
  ze-core .in-CwFwE-sorts.CwFwE-core.↓[] {t = t} = {!  !}
  ze-core .in-CwFwE-sorts.CwFwE-core.↑↓ = {!!}
  ze-core .in-CwFwE-sorts.CwFwE-core.↓↑ = {!!}
  ze-core .in-CwFwE-sorts.CwFwE-core.pz∘⁺≡⁺∘pz' = {! !}


