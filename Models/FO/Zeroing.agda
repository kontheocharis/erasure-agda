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
  ze-core .CwFwE-core.↓[] {t = t} = {! splitl ? !}
  ze-core .CwFwE-core.↑↓ = {!!}
  ze-core .CwFwE-core.↓↑ = [id]
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
    Σ[ iΓ ∈ (⟦ ⟦ Γ ⟧ᶜ ⟧ᶜ ≡ ⟦ Γ ⟧ᶜ) true ]
    (⟦ ↑↑ ⟧ˢ ≡[ ap-Subᶜ refl (iΓ .witness) ] id) true
  nn-sorts .Subᴰ (↑↑Γ , iΓ , pΓ) (↑↑Δ , iΔ , pΔ) σ =
    Σ[ iσ ∈ (⟦ ⟦ σ ⟧ˢ ⟧ˢ ≡[ ap-Subᶜ (iΓ .witness) (iΔ .witness) ] ⟦ σ ⟧ˢ) true ]
    (⟦ σ ⟧ˢ ∘ ↑↑Γ ≡ ↑↑Δ ∘ σ) true
  nn-sorts .Tyᴰ (↑↑Γ , iΓ , pΓ) A =
    Σ[ iA ∈ (⟦ ⟦ A ⟧ᵀ ⟧ᵀ ≡[ ap-Tyᶜ (iΓ .witness) ] ⟦ A ⟧ᵀ) true ]
    (⟦ A ⟧ᵀ [ ↑↑Γ ]T ≡ A) true  
  nn-sorts .#∈ᴰ _ _ =  𝟙 
  nn-sorts .Tmᴰ (↑↑Γ , iΓ , pΓ) z (iA , pA) a =
    Σ[ ia ∈ (⟦ ⟦ a ⟧ᵗ ⟧ᵗ ≡[ ap-Tmᶜ (iΓ .witness) (iA .witness) ] ⟦ a ⟧ᵗ) true ]
    (⟦ a ⟧ᵗ [ ↑↑Γ ] ≡[ ap-Tm (pA .witness) ] a) true
  nn-sorts .Tmᴰ (↑↑Γ , iΓ , pΓ) ω (iA , pA) a =
    Σ[ ia ∈ (⟦ ⟦ a ⟧ᵗ ⟧ᵗ ≡[ ap-Tmᶜ (iΓ .witness) (iA .witness) ] ⟦ a ⟧ᵗ) true ]
    (⟦ a ⟧ᵗ [ ↑↑Γ ] ≡[ ap-Tm (pA .witness) ] (↓* a)) true

  -- various congruence rules
  opaque
    unfolding coe
    ap-[]₀ : (p : σ ≡ τ) → t [ σ ] ≡[ ap-Tm (ap-[]T₀ p) ] t [ τ ]
    ap-[]₀ refl = refl

    ap-[]₁ : ∀ {t : Tm Γ i A} {u : Tm Γ i B} (p : A ≡ B) → t ≡[ ap-Tm p ] u → t [ σ ] ≡[ ap-Tm (ap-[]T₁ p) ] u [ σ ]
    ap-[]₁ refl refl = refl

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


  nn-ctors : CwFwEᴰ-core nn-sorts core
  nn-ctors .idᴰ {Γ = Γ} {Γᴰ = (↑↑Γ , iΓ , pΓ)} = by (ap-id (iΓ .witness)) , by (trans id∘ (sym ∘id))
  nn-ctors ._∘ᴰ_ {Δᴰ = (_ , iΔ , _)} {Θᴰ = (_ , iΘ , _)} {σ = σ} {Γᴰ = (_ , iΓ , _)} {τ = τ} (iσ , pσ) (iτ , pτ)
    =  by (ap-∘ (iΔ .witness) (iΘ .witness) (iΓ .witness) ( iσ .witness) ( iτ .witness))
      , by (trans (sym assoc) (trans (cong (⟦ σ ⟧ˢ ∘_) (pτ .witness))
      (trans assoc (trans (cong (_∘ τ) (pσ .witness)) (sym assoc)))))
  nn-ctors .assocᴰ = refl
  nn-ctors .∘idᴰ = refl
  nn-ctors .id∘ᴰ = refl
  nn-ctors .∙ᴰ = id , by refl , by (dep refl)
  nn-ctors .εᴰ {Γᴰ = (_ , iΓ , _)} = by (ap-ε (iΓ .witness)) , by (trans (sym ∃!ε) (sym id∘))
  nn-ctors .∃!εᴰ = refl
  nn-ctors ._[_]Tᴰ {Δᴰ = (↑↑Δ , iΔ , pΔ)} {Γᴰ = (↑↑Γ , iΓ , pΓ)} {σ = σ} (iA , pA) (iσ , pσ)
    =  by (ap-[]T (iΓ .witness) (iΔ .witness) (iA .witness) (iσ .witness))
      , by (trans (sym [∘]T) (trans (ap-[]T₀ (pσ .witness))
      (trans [∘]T (ap-[]T₁ (pA .witness)))))
  nn-ctors ._[_]ᴰ {Δᴰ = (↑↑Δ , iΔ , pΔ)} {i = z} {Aᴰ = (iA , pA)} {Γᴰ = (↑↑Γ , iΓ , pΓ)} (ia , pa) (iσ , pσ)
    =  by (ap-[] (iΓ .witness) (iΔ .witness) (iA .witness) (iσ .witness) (ia .witness))
      , by (transᴰ {p = ap-Tm (sym [∘]T)} (symᴰ [∘])
      (transᴰ {p = ap-Tm (ap-[]T₀ (pσ .witness))} (ap-[]₀ (pσ .witness))
      (transᴰ {p = ap-Tm [∘]T} [∘] (ap-[]₁ (pA .witness) (pa .witness)))))
  nn-ctors ._[_]ᴰ {Δᴰ = (↑↑Δ , iΔ , pΔ)} {i = ω} {Aᴰ = (iA , pA)} {Γᴰ = (↑↑Γ , iΓ , pΓ)} (ia , pa) (iσ , pσ)
    = by (ap-[] (iΓ .witness) (iΔ .witness) (iA .witness) (iσ .witness) (ia .witness))
      , by (transᴰ {p = ap-Tm (sym [∘]T)} (symᴰ [∘])
      (transᴰ {p = ap-Tm (ap-[]T₀ (pσ .witness))} (ap-[]₀ (pσ .witness))
      (transᴰ {p = ap-Tm [∘]T} [∘] (trans (ap-[]₁ (pA .witness) (pa .witness)) ↓*[]))))
  nn-ctors ._[_]#ᴰ = λ _ _ → tt
  nn-ctors .[id]Tᴰ = refl
  nn-ctors .[id]ᴰ {i = z} = refl
  nn-ctors .[id]ᴰ {i = ω} = refl
  nn-ctors .[id]#ᴰ = refl
  nn-ctors .[∘]Tᴰ = refl
  nn-ctors .[∘]ᴰ {i = z} = refl
  nn-ctors .[∘]ᴰ {i = ω} = refl
  nn-ctors .[∘]#ᴰ = refl
  nn-ctors ._▷ᴰ[_]_ {Γ = Γ} {A = A} (↑↑ , iΓ , pΓ) z (iA , pA)
    = ((↑↑ ∘ p) ,, coe (ap-Tm (sym (trans [∘]T (ap-[]T₁ (pA .witness))))) q) 
      , by (ap-▷[] (iΓ .witness) (iA .witness))
      , by (trans (ap-,, refl (iΓ .witness) {t = coe _ q}
      (trans (ap-∘ refl (iΓ .witness) refl (pΓ .witness) refl) (trans id∘ (ap-p refl  reflᴰ)))
      (iA .witness) (splitl {x = ⟦ q ⟧ᵗ} {q = ap-Tmᶜ refl {! !}} (ap-q (iΓ .witness) (iA .witness)))) p,q)
  (nn-ctors ▷ᴰ[ ↑↑ , iΓ , pΓ ] ω) (iA , pA)
    = ((↑↑ ∘ p) ,, coe (ap-Tm (sym (trans [∘]T (ap-[]T₁ (pA .witness))))) (↓* q))
      , by (ap-▷[] (iΓ .witness) (iA .witness))
      , {!!}
  nn-ctors .pᴰ {Γᴰ = (↑↑ , iΓ , pΓ)} {i = z} {Aᴰ = (iA , pA)}
    = by (ap-p (iΓ .witness) (iA .witness))
      , by p∘, 
  nn-ctors .pᴰ {Γᴰ = (↑↑ , iΓ , pΓ)} {i = ω} {Aᴰ = (iA , pA)}
    = by (ap-p (iΓ .witness) (iA .witness))
      , by p∘,
  nn-ctors .qᴰ {Γᴰ = (↑↑ , iΓ , pΓ)} {i = z} {Aᴰ = (iA , pA)}
    = by (ap-q (iΓ .witness) (iA .witness))
      ,  by (trans ({! !}) q[,])
  nn-ctors .qᴰ {Γᴰ = (↑↑ , iΓ , pΓ)} {i = ω} {Aᴰ = (iA , pA)}
    = by (ap-q (iΓ .witness) (iA .witness))
      ,  by (trans ({! !}) q[,])
  _,,ᴰ_ nn-ctors {Γᴰ = (↑↑Γ , iΓ , pΓ)} {Δᴰ = (↑↑Δ , iΔ , pΔ)} {i = z} {Aᴰ = (iA , pA)}  (iσ , pσ) (it , pt)
    = by (ap-,, (iΓ .witness) (iΔ .witness) (iσ .witness) (iA .witness) (it .witness)) , {!!}
  _,,ᴰ_ nn-ctors {Γᴰ = (↑↑Γ , iΓ , pΓ)} {Δᴰ = (↑↑Δ , iΔ , pΔ)} {i = ω} {Aᴰ = (iA , pA)}  (iσ , pσ) (it , pt)
    = by (ap-,, (iΓ .witness) (iΔ .witness) (iσ .witness) (iA .witness) (it .witness)) , {!!}
  nn-ctors .,∘ᴰ = refl
  nn-ctors .p,qᴰ = refl
  nn-ctors .p∘,ᴰ = refl
  nn-ctors .q[,]ᴰ {i = z} = refl
  nn-ctors .q[,]ᴰ {i = ω} = refl
  nn-ctors ._▷#ᴰ (↑↑ , iΓ , pΓ)
    = (↑↑ ∘ p#) , iΓ , by (trans (cong (coe _) ∘id) (pΓ .witness))
  nn-ctors .p#ᴰ {Γᴰ = (↑↑ , iΓ , pΓ)} = by (ap-id (iΓ .witness)) , by id∘
  nn-ctors .q#ᴰ {Γᴰ = (↑↑ , iΓ , pΓ)} = tt
  _,#ᴰ_ nn-ctors {Γᴰ = ↑↑Γ , iΓ , pΓ} {Δᴰ = ↑↑Δ , iΔ , pΔ} {σ = σ} (iσ , pσ) tt
    = iσ , by (trans (pσ .witness) (trans (cong (↑↑Δ ∘_) (sym (p∘,#))) assoc))
  nn-ctors .,#∘ᴰ = refl
  nn-ctors .p,#qᴰ = refl
  nn-ctors .p∘,#ᴰ = refl
  nn-ctors .q[,#]ᴰ = refl
  nn-ctors .↓ᴰ {Γᴰ = (↑↑ , iΓ , pΓ)} {Aᴰ = (iA , pA)} (it , pt)
    = by ({! splitl ?!}) , by {!!}
  nn-ctors .↑ᴰ {Γᴰ = (↑↑ , iΓ , pΓ)} {Aᴰ = (iA , pA)} (it , pt)
    = by (ap-[] (iΓ .witness) (iΓ .witness) (iA .witness) ( ap-id (iΓ .witness)) (it .witness)) , {! !}
  nn-ctors .↓[]ᴰ = refl
  nn-ctors .↑↓ᴰ = refl
  nn-ctors .↓↑ᴰ = refl
  nn-ctors .pz∘⁺≡⁺∘pz'ᴰ = refl

  nn : CwFwEᴰ syn
  nn .sortsᴰ = nn-sorts
  nn .coreᴰ = nn-ctors
  nn .Π-strᴰ = {!!}
  nn .U-strᴰ = {!!}


  ⟦↑↑⟧≡↑↑ : {Γ : Con}
    → (let (↑↑Γ , _ , _) = CwFwE-elim.⟦_⟧ᶜ nn (Γ))
    → (let (↑↑⟦Γ⟧ , _ , _) = CwFwE-elim.⟦_⟧ᶜ nn (⟦ Γ ⟧ᶜ))
    → ⟦ ↑↑Γ ⟧ˢ ≡ ↑↑⟦Γ⟧
  ⟦↑↑⟧≡↑↑ {Γ} = (CwFwE-elim-Con.⟦_⟧
    (λ Γ → (let (↑↑Γ , _ , _) = CwFwE-elim.⟦_⟧ᶜ nn (Γ))
    → (let (↑↑⟦Γ⟧ , _ , _) = CwFwE-elim.⟦_⟧ᶜ nn (⟦ Γ ⟧ᶜ))
    → (⟦ ↑↑Γ ⟧ˢ ≡ ↑↑⟦Γ⟧) true)
      (by refl)
      (λ Γ A pr → by (cong (λ σ → ((σ ∘ p) ,, coe (ap-Tmᶜ refl {! !}) q)) (pr .witness)))
      (λ Γ A pr → by ({! !}))
      ( λ Γ pr → by (trans ∘id (pr .witness)) ) Γ) .witness

  opaque
    unfolding coe

    types-need-nothing : Ty Γ ≃ Ty ⟦ Γ ⟧ᶜ
    types-need-nothing .to = ⟦_⟧ᵀ
    types-need-nothing {Γ = Γ} .from A =
      let (↑↑ , iΓ , pΓ) = CwFwE-elim.⟦_⟧ᶜ nn Γ in
      let (iA , pA) = CwFwE-elim.⟦_⟧ᵀ nn A in (A [ ↑↑ ]T)
    types-need-nothing {Γ = Γ} .to-from A =
      let (↑↑ , iΓ , pΓ) = CwFwE-elim.⟦_⟧ᶜ nn Γ in
      let (iA , pA) = CwFwE-elim.⟦_⟧ᵀ nn A in
      let (i↑↑ , p↑↑) =  CwFwE-elim.⟦_⟧ˢ nn ↑↑ in
      trans (ap-[]T₀ (⟦↑↑⟧≡↑↑ {Γ = Γ})) (pA .witness)  
    types-need-nothing {Γ = Γ} .from-to A =
      let (iA , pA) = CwFwE-elim.⟦_⟧ᵀ nn A in pA .witness

    erased-terms-need-nothing : Tm Γ z A ≃ Tm ⟦ Γ ⟧ᶜ z ⟦ A ⟧ᵀ
    erased-terms-need-nothing .to = ⟦_⟧ᵗ
    erased-terms-need-nothing {Γ = Γ} {A = A} .from a =
      let (↑↑ , iΓ , pΓ) = CwFwE-elim.⟦_⟧ᶜ nn Γ in
      let (iA , pA) = CwFwE-elim.⟦_⟧ᵀ nn A in
      let (ia , pa) = CwFwE-elim.⟦_⟧ᵗ nn a in
      let (i↑↑ , p↑↑) =  CwFwE-elim.⟦_⟧ˢ nn ↑↑ in
      coe (ap-Tm (pA .witness)) (a [ ↑↑ ])
    erased-terms-need-nothing {Γ = Γ} .to-from a =
      {!!}
    erased-terms-need-nothing {Γ = Γ} .from-to a = {!!}
