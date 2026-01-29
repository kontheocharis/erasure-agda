{-# OPTIONS --type-in-type #-}
module Models.FO.Zeroing where

open import Utils
open import Theories.CwFwE
open import Data.Unit renaming (⊤ to 𝟙)
open import Data.Product
open import Mode


module _ (e : CwFwE)  where
  open CwFwE
  open CwFwE-sorts (e .sorts)
  open in-CwFwE-sorts (e .sorts)
  open CwFwE-core (e .core)
  open in-CwFwE-core (e .core)

  ze-sorts : CwFwE-sorts
  ze-sorts .CwFwE-sorts.Con = Con
  ze-sorts .CwFwE-sorts.Sub = Sub
  ze-sorts .CwFwE-sorts.Ty = Ty
  ze-sorts .CwFwE-sorts.#∈ Γ = 𝟙
  ze-sorts .CwFwE-sorts.Tm Γ i A = Tm Γ z A 

  ze-core : in-CwFwE-sorts.CwFwE-core ze-sorts
  ze-core .CwFwE-core.id = id
  ze-core .CwFwE-core._∘_ = _∘_
  ze-core .CwFwE-core.assoc = assoc
  ze-core .CwFwE-core.∘id = ∘id
  ze-core .CwFwE-core.id∘ = id∘
  ze-core .CwFwE-core.∙ = ∙
  ze-core .CwFwE-core.ε = ε
  ze-core .CwFwE-core.∃!ε = ∃!ε
  ze-core .CwFwE-core._[_]T = _[_]T
  ze-core .CwFwE-core._[_] = _[_]
  ze-core .CwFwE-core._[_]# = λ t σ → tt
  ze-core .CwFwE-core.[id]T = [id]T
  ze-core .CwFwE-core.[id] = [id]
  ze-core .CwFwE-core.[id]# = refl
  ze-core .CwFwE-core.[∘]T = [∘]T
  ze-core .CwFwE-core.[∘] = [∘]
  ze-core .CwFwE-core.[∘]# = refl
  (ze-core CwFwE-core.▷[ Γ ] i) A = Γ ▷[ z ] A
  ze-core .CwFwE-core.p = p
  ze-core .CwFwE-core.q = q
  ze-core .CwFwE-core._,,_ = _,,_
  ze-core .CwFwE-core.,∘ = ,∘
  ze-core .CwFwE-core.p,q = p,q
  ze-core .CwFwE-core.p∘, = p∘,
  ze-core .CwFwE-core.q[,] = q[,]
  (ze-core CwFwE-core.▷#) Γ = Γ
  ze-core .CwFwE-core.p# = id
  ze-core .CwFwE-core.q# = tt
  ze-core .CwFwE-core._,#_ = λ σ π → σ
  ze-core .CwFwE-core.,#∘ = refl
  ze-core .CwFwE-core.p,#q = refl
  ze-core .CwFwE-core.p∘,# = id∘
  ze-core .CwFwE-core.q[,#] = refl
  ze-core .CwFwE-core.↓ x = coe (cong (Tm _ _) [id]T) x
  ze-core .CwFwE-core.↑ x = x [ id ]
  ze-core .CwFwE-core.↓[] {t = t} = {! ↓[] !}
  ze-core .CwFwE-core.↑↓ = {!!}
  ze-core .CwFwE-core.↓↑ = {!!}
  ze-core .CwFwE-core.pz∘⁺≡⁺∘pz' = {! !}

  ze : CwFwE
  ze .sorts = ze-sorts
  ze .core = ze-core
  ze .Π-str = {!!}
  ze .U-str = {!!}

  zeᴰ : CwFwEᴰ e
  zeᴰ = CwFwE-uniform.nᴰ e ze


module need-nothing where

  open CwFwE-syntax
  
  ze-syn = ze syn
  
  open CwFwE-uniform syn (ze syn)
  open CwFwE-elim nᴰ

  open CwFwEᴰ
  open CwFwEᴰ-sorts
  open in-CwFwEᴰ-sorts
  open CwFwEᴰ-core
  open in-CwFwEᴰ-core
  open Π-structureᴰ
  open U-structureᴰ

  nn-sorts : CwFwEᴰ-sorts sorts
  nn-sorts .Conᴰ Γ =
    Σ[ ↑↑ ∈ Sub Γ ⟦ Γ ⟧ᶜ ]
    Σ[ idemp ∈ (⟦ ⟦ Γ ⟧ᶜ ⟧ᶜ ≡ ⟦ Γ ⟧ᶜ) true ]
    (⟦ ↑↑ ⟧ˢ ≡[ ap-Subᶜ refl (idemp .witness) ] id) true
  nn-sorts .Subᴰ (↑↑Γ , pΓ) (↑↑Δ , pΔ) σ = (⟦ σ ⟧ˢ ∘ ↑↑Γ ≡ ↑↑Δ ∘ σ) true
  nn-sorts .Tyᴰ (↑↑Γ , pΓ) A = (⟦ A ⟧ᵀ [ ↑↑Γ ]T ≡ A) true  
  nn-sorts .#∈ᴰ _ _ =  𝟙 
  nn-sorts .Tmᴰ (↑↑Γ , pΓ) z pA a = (⟦ a ⟧ᵗ [ ↑↑Γ ] ≡[ ap-Tm (pA .witness) ] a) true
  nn-sorts .Tmᴰ _ ω _ _ = 𝟙

  
  nn-ctors : CwFwEᴰ-core nn-sorts core
  nn-ctors .idᴰ = by (trans id∘ (sym ∘id))
  nn-ctors ._∘ᴰ_ {σ = σ} {τ = τ} pσ pτ
    = by (trans (sym assoc) (trans (cong (⟦ σ ⟧ˢ ∘_) (pτ .witness))
      (trans assoc (trans (cong (_∘ τ) (pσ .witness)) (sym assoc)))))
  nn-ctors .assocᴰ = refl
  nn-ctors .∘idᴰ = refl
  nn-ctors .id∘ᴰ = refl
  nn-ctors .∙ᴰ =  id , by refl , by (dep refl)
  nn-ctors .εᴰ = by (trans (sym ∃!ε) (sym id∘))
  nn-ctors .∃!εᴰ = refl
  nn-ctors ._[_]Tᴰ {Δᴰ = (↑↑Δ , pΔ)} {Γᴰ = (↑↑Γ , pΓ)} {σ = σ} pA pσ
    = by (trans (sym [∘]T) (trans (ap-[]T₀ (pσ .witness))
      (trans [∘]T (ap-[]T₁ (pA .witness)))))
  _[_]ᴰ nn-ctors {Δᴰ = (↑↑Δ , pΔ)} {i = z} {Aᴰ = pA} {Γᴰ = (↑↑Γ , pΓ)}  pa pσ
    = by (transᴰ {p = ap-Tm (sym [∘]T)} (symᴰ [∘])
      (transᴰ {p = ap-Tm (ap-[]T₀ (pσ .witness))} (ap-[]₀ (pσ .witness))
      (transᴰ {p = ap-Tm [∘]T} [∘] (ap-[]₁ (pA .witness) (pa .witness)))))
  _[_]ᴰ nn-ctors {i = ω} = λ _ _ → tt
  nn-ctors ._[_]#ᴰ = λ _ _ → tt
  nn-ctors .[id]Tᴰ = refl
  nn-ctors .[id]ᴰ {i = z} = refl
  nn-ctors .[id]ᴰ {i = ω} = refl
  nn-ctors .[id]#ᴰ = refl
  nn-ctors .[∘]Tᴰ = refl
  nn-ctors .[∘]ᴰ {i = z} = refl
  nn-ctors .[∘]ᴰ {i = ω} = refl
  nn-ctors .[∘]#ᴰ = refl
  (nn-ctors ▷ᴰ[ ↑↑ , idemp , pΓ ] z) pA = ((↑↑ ∘ p) ,, {! q!})  , {!!} , {!!}
  (nn-ctors ▷ᴰ[ Γᴰ ] ω) A = {!!}
  nn-ctors .pᴰ = {! !}
  nn-ctors .qᴰ = {!!}
  nn-ctors ._,,ᴰ_ = {! !}
  nn-ctors .,∘ᴰ = {! !}
  nn-ctors .p,qᴰ = {!!}
  nn-ctors .p∘,ᴰ = {!!}
  nn-ctors .q[,]ᴰ = {!!}
  nn-ctors ▷#ᴰ = {!!}
  nn-ctors .p#ᴰ = {!!}
  nn-ctors .q#ᴰ = {!!}
  nn-ctors ._,#ᴰ_ = {!!}
  nn-ctors .,#∘ᴰ = {!!}
  nn-ctors .p,#qᴰ = {!!}
  nn-ctors .p∘,#ᴰ = {!!}
  nn-ctors .q[,#]ᴰ = {!!}
  nn-ctors .↓ᴰ = {!!}
  nn-ctors .↑ᴰ = {!!}
  nn-ctors .↓[]ᴰ = {!!}
  nn-ctors .↑↓ᴰ = {!!}
  nn-ctors .↓↑ᴰ = {!!}
  nn-ctors .pz∘⁺≡⁺∘pz'ᴰ = {!!}

  nn : CwFwEᴰ syn
  nn .sortsᴰ = nn-sorts
  nn .coreᴰ = {!!}
  nn .Π-strᴰ = {!!}
  nn .U-strᴰ = {!!}

