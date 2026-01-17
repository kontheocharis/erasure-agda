module Models.FO.Quantitative where

open import Utils
open import Theories.CwFwE
open import Theories.QCwF
open import Data.Unit renaming (⊤ to 𝟙)
open import Data.Product
open import Mode

open CwFwE-sorts
open in-CwFwE-sorts

module _ (e-sorts : CwFwE-sorts) (e-core : CwFwE-core e-sorts) where
  open CwFwE-core e-core
  open in-CwFwE-core e-sorts e-core

  open QCwF-sorts
  open in-QCwF-sorts

  q-sorts : QCwF-sorts
  q-sorts .Con = e-sorts .Con
  q-sorts .Conω Γ = 𝟙
  q-sorts .Sub Γ Δ = e-sorts .Sub (Γ ▷#) (Δ ▷#)
  q-sorts .Subω {Γ} {Δ} _ _ σ = Σ[ σω ∈ e-sorts .Sub Γ Δ ] ((σω ⁺# ≡ σ) true) 
  q-sorts .Ty Γ = e-sorts .Ty Γ
  q-sorts .Tm Γ A = e-sorts .Tm Γ z A
  q-sorts .Tmω {Γ} _ A t = Σ[ tω ∈ e-sorts .Tm Γ ω A ] ( ((↓* tω) ≡ t) true)

  q-core : QCwF-core q-sorts
  q-core .QCwF-core.id = id
  q-core .QCwF-core._∘_ = _∘_
  q-core .QCwF-core.assoc = assoc
  q-core .QCwF-core.∘id = ∘id
  q-core .QCwF-core.id∘ = id∘
  q-core .QCwF-core.idω = id , {!!}
  (q-core QCwF-core.∘ω σω) τω = (σω .proj₁ ∘ τω .proj₁) , by {! !} 
  q-core .QCwF-core.assocω = {! !}
  q-core .QCwF-core.∘idω = {!!}
  q-core .QCwF-core.id∘ω = {!!}
  q-core .QCwF-core.∙ = {!!}
  q-core .QCwF-core.ε = {!!}
  q-core .QCwF-core.∃!ε = {!!}
  q-core .QCwF-core.∙ω = {!!}
  q-core .QCwF-core.εω = {!!}
  q-core .QCwF-core.∃!εω = {!!}
  (q-core QCwF-core.[ A ]T) σ = {! A [ σ ]T!}
  q-core .QCwF-core._[_] = {!!}
  q-core .QCwF-core.[id]T = {!!}
  q-core .QCwF-core.[id] = {!!}
  q-core .QCwF-core.[∘]T = {!!}
  q-core .QCwF-core.[∘] = {!!}
  q-core .QCwF-core._[_]ω = {!!}
  q-core .QCwF-core.[id]ω = {!!}
  q-core .QCwF-core.[∘]ω = {!!}
  q-core .QCwF-core._▷_ = {!!}
  q-core .QCwF-core.p = {!!}
  q-core .QCwF-core.q = {!!}
  q-core .QCwF-core._,,_ = {!!}
  q-core .QCwF-core.,∘ = {!!}
  q-core .QCwF-core.p,q = {!!}
  q-core .QCwF-core.p∘, = {!!}
  q-core .QCwF-core.q[,] = {!!}
  q-core .QCwF-core._▷ω_ = {!!}
  q-core .QCwF-core.pω = {!!}
  q-core .QCwF-core.qω = {!!}
  q-core .QCwF-core._,,ω_ = {!!}
  q-core .QCwF-core.,∘ω = {!!}
  q-core .QCwF-core.p,qω = {!!}
  q-core .QCwF-core.p∘,ω = {!!}
  q-core .QCwF-core.q[,]ω = {!!}
  q-core .QCwF-core._▷z_ = {!!}
  q-core .QCwF-core.pz = {!!}
  q-core .QCwF-core._,,z_ = {!!}
  q-core .QCwF-core.,∘z = {!!}
  q-core .QCwF-core.p,qz = {!!}
  q-core .QCwF-core.p∘,z = {!!}
