{-# OPTIONS --type-in-type --lossy-unification #-}
module Models.FO.Zeroing where

open import Utils
open import Theories.CwFwE
open import Data.Unit renaming (⊤ to 𝟙)
open import Data.Product
open import Mode

-- The zeroing model
-- Interprets all terms as erased terms, and # as unit.

module _ (e : CwFwE)  where
  open CwFwE
  open CwFwE-sorts (e .sorts)
  open in-CwFwE-sorts (e .sorts)
  open CwFwE-core (e .core)
  open in-CwFwE-core (e .core)
  open Π-structure (e .Π-str)
  open U-structure (e .U-str)

  ze-sorts : CwFwE-sorts
  ze-sorts .CwFwE-sorts.Con = Con
  ze-sorts .CwFwE-sorts.Sub = Sub
  ze-sorts .CwFwE-sorts.Ty = Ty
  ze-sorts .CwFwE-sorts.#∈ Γ = 𝟙
  ze-sorts .CwFwE-sorts.Tm Γ i A = Tm Γ z A 
  ze-sorts .CwFwE-sorts.#-prop p₁ q₁ = refl

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
  ze-core .CwFwE-core.↓ x = coe (ap-Tm [id]T) x
  ze-core .CwFwE-core.↑ x = x [ id ]
  ze-core .CwFwE-core.↓[] {t = t} = undep (splitr (splitr (ap-[] refl refl (dep (sym [id]T)) (dep (sym ∘id)) (splitl reflᴰ)))) 
  ze-core .CwFwE-core.↑↓ = undep (transᴰ {q = ap-Tm (sym [id]T)} [id] (splitl reflᴰ)) 
  ze-core .CwFwE-core.↓↑ = [id]

  ze-Π : in-CwFwE-sorts.in-CwFwE-core.Π-structure ze-sorts ze-core
  ze-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Π i A B = Π i A B
  ze-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Π[] = Π[]
  ze-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam {i = z} f
    = ↓ (coe (ap-Tm (sym Π[])) (lam (coe (ap-Tm {! !}) ((↑ (f [ (p# ∘ p) ,, coe (ap-Tm (sym [∘]T)) q ])) [  id ,# (q# [ p ]#) ]))) )
  ze-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam {i = ω} f = {! !}
  ze-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.lam[] = {! !}
  ze-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.ap = {! !}
  ze-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Πβ = {! !}
  ze-Π .in-CwFwE-sorts.in-CwFwE-core.Π-structure.Πη = {!!}

  ze-U : in-CwFwE-sorts.in-CwFwE-core.U-structure ze-sorts ze-core
  ze-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.U = U
  ze-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.U[] = U[]
  ze-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.El = El
  ze-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.El[] = El[]
  ze-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.code = code
  ze-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.code[] = code[]
  ze-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.El-code = El-code
  ze-U .in-CwFwE-sorts.in-CwFwE-core.U-structure.code-El = code-El

  ze : CwFwE
  ze .sorts = ze-sorts
  ze .core = ze-core
  ze .Π-str = ze-Π
  ze .U-str = ze-U

  zeᴰ : CwFwEᴰ e
  zeᴰ = CwFwE-uniform.nᴰ e ze 


-- Here we prove that erased terms don't depend on the erasure marker,
-- or relevant context bindings. See the final theorems at the bottom of the file.
--
-- To do this, we perform an induction over the syntax, to prove some simultaneous lemmas:
-- 1. There is a ↑↑ : Sub Γ 0Γ that becomes id under zeroing
-- 2. For types, (0A)[↑↑] ≡ A, and for terms (0a)[↑↑] ≡ ↓*a
-- 3. Zeroing is idempotent

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

  σ≡,, : ∀ {Γ Δ A} {σ : Sub Γ (Δ ▷[ i ] A)} → σ ≡ ((p ∘ σ) ,, coe (ap-Tm (sym [∘]T)) (q [ σ ]))
  σ≡,, {σ = σ} = trans (sym id∘) (trans (cong (_∘ σ) (sym (p,q))) ,∘)

  σ≡,# : ∀ {Γ Δ} {σ : Sub Γ (Δ ▷#)} → σ ≡ ((p# ∘ σ) ,# (q# [ σ ]#))
  σ≡,# {σ = σ} = trans (sym id∘) (trans (cong (_∘ σ) (sym (p,#q))) ,#∘)


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
  nn-sorts .Tmᴰ (↑↑Γ , iΓ , pΓ) i (iA , pA) a =
    Σ[ ia ∈ (⟦ ⟦ a ⟧ᵗ ⟧ᵗ ≡[ ap-Tmᶜ (iΓ .witness) (iA .witness) ] ⟦ a ⟧ᵗ) true ]
    (⟦ a ⟧ᵗ [ ↑↑Γ ] ≡[ ap-Tm (pA .witness) ] (↓* a)) true
  nn-sorts .#-propᴰ p₁ q₁ prf = refl

  opaque
    unfolding ↓*ᴰ

    p#-inj : #∈ Γ → {t : Tm Γ i A} → t [ p# ] ≡ u [ p# ] → t ≡ u
    p#-inj mrk prf =
      undep (transᴰ (symᴰ (transᴰ (ap-[]₀ p∘,#) [id]))
      (transᴰ (transᴰ [∘] (transᴰ (ap-[]₁ {σ = (id ,# mrk)} refl (dep prf)) (symᴰ [∘])))
      (transᴰ (ap-[]₀ p∘,#) [id])))

    inj-↑[p#] : {t u : Tm (Γ ▷#) ω (A [ p# ]T)} → ↓ (t [ p# ]) ≡ ↓ (u [ p# ]) → ↓ t ≡ ↓ u
    inj-↑[p#] prf = cong ↓ (p#-inj q# (trans (sym ↑↓) (trans (cong ↑ prf) ↑↓)))

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
        , by (transᴰ (symᴰ [∘])
        (transᴰ (ap-[]₀ (pσ .witness))
        (transᴰ [∘] (ap-[]₁ (pA .witness) (pa .witness)))))
    nn-ctors ._[_]ᴰ {Δᴰ = (↑↑Δ , iΔ , pΔ)} {i = ω} {Aᴰ = (iA , pA)} {Γᴰ = (↑↑Γ , iΓ , pΓ)} (ia , pa) (iσ , pσ)
      = by (ap-[] (iΓ .witness) (iΔ .witness) (iA .witness) (iσ .witness) (ia .witness))
        , by (transᴰ (symᴰ [∘])
        (transᴰ (ap-[]₀ (pσ .witness))
        (transᴰ [∘] (trans (ap-[]₁ (pA .witness) (pa .witness)) ↓*[]))))
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
        , by (transᴰ (ap-,, refl (iΓ .witness)
        (transᴰ (ap-∘ refl (iΓ .witness) refl (pΓ .witness) refl) (dep (trans id∘ reflᴰ)))
        (iA .witness) (splitl reflᴰ)) (dep p,q))
    nn-ctors ._▷ᴰ[_]_ {Γ = Γ} {A = A} (↑↑ , iΓ , pΓ) ω (iA , pA)
      = ((↑↑ ∘ p) ,, coe (ap-Tm (sym (trans [∘]T (ap-[]T₁ (pA .witness))))) (↓* q))
        , by (ap-▷[] (iΓ .witness) (iA .witness))
        , by (transᴰ (ap-,, refl (iΓ .witness)
        (transᴰ (ap-∘ refl (iΓ .witness) refl (pΓ .witness) refl) (dep (trans id∘ reflᴰ)))
        (iA .witness) (splitl reflᴰ)) (transᴰ (ap-,, refl refl reflᴰ reflᴰ (splitl (transᴰ [id] reflᴰ))) (dep p,q)))
    nn-ctors .pᴰ {Γᴰ = (↑↑ , iΓ , pΓ)} {i = z} {Aᴰ = (iA , pA)}
      = by (ap-p (iΓ .witness) (iA .witness))
        , by p∘, 
    nn-ctors .pᴰ {Γᴰ = (↑↑ , iΓ , pΓ)} {i = ω} {Aᴰ = (iA , pA)}
      = by (ap-p (iΓ .witness) (iA .witness))
        , by p∘,
    nn-ctors .qᴰ {Γ = Γ} {Γᴰ = (↑↑ , iΓ , pΓ)} {i = z} {A = A} {Aᴰ = (iA , pA)}
      = by (ap-q (iΓ .witness) (iA .witness))
        , by (transᴰ (transᴰ {q = ap-Tm (trans [∘]T (trans (ap-[]T₁ (pA .witness)) (sym (trans (ap-[]T₀ p,q) [id]T))))}
          q[,] (splitl (symᴰ q[,]))) q[,])
    nn-ctors .qᴰ {Γᴰ = (↑↑ , iΓ , pΓ)} {i = ω} {Aᴰ = (iA , pA)}
      = by (ap-q (iΓ .witness) (iA .witness))
        , by (transᴰ {q = ap-Tm (trans [∘]T (ap-[]T₁ (pA .witness)))} q[,] (splitl reflᴰ))
    _,,ᴰ_ nn-ctors {Γᴰ = (↑↑Γ , iΓ , pΓ)} {Δᴰ = (↑↑Δ , iΔ , pΔ)} {i = z} {Aᴰ = (iA , pA)} (iσ , pσ) (it , pt)
      = by (ap-,, (iΓ .witness) (iΔ .witness) (iσ .witness) (iA .witness) (it .witness))
        ,  by (trans ,∘ (trans (undep (ap-,, refl refl
          (dep (trans (pσ .witness) (sym (trans (sym assoc) (cong (↑↑Δ ∘_) p∘,))))) reflᴰ
          (splitr (splitl (transᴰ (pt .witness) (symᴰ (transᴰ
          (ap-[] refl refl (dep (trans [∘]T (ap-[]T₁ (pA .witness)))) reflᴰ (splitl reflᴰ)) q[,])))))))
          (sym (,∘)))) 
    _,,ᴰ_ nn-ctors {Γᴰ = (↑↑Γ , iΓ , pΓ)} {Δᴰ = (↑↑Δ , iΔ , pΔ)} {i = ω} {Aᴰ = (iA , pA)}  (iσ , pσ) (it , pt)
      = by (ap-,, (iΓ .witness) (iΔ .witness) (iσ .witness) (iA .witness) (it .witness))
        ,  by (trans ,∘ (trans (undep (ap-,, refl refl
          (dep (trans (pσ .witness) (sym (trans (sym assoc) (cong (↑↑Δ ∘_) p∘,))))) reflᴰ
          (splitr (splitl (transᴰ (pt .witness) (symᴰ (transᴰ
          (ap-[] refl refl (dep (trans [∘]T (ap-[]T₁ (pA .witness)))) reflᴰ (splitl reflᴰ)) ↓*q[,])))))))
          (sym (,∘)))) 
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
    nn-ctors .↓ᴰ {Γ = Γ} {Γᴰ = (↑↑ , iΓ , pΓ)} {Aᴰ = (iA , pA)} (it , pt)
      =  by (splitr (splitl (it .witness))) ,  by (transᴰ (symᴰ (transᴰ {q = ap-Tm (sym (pA .witness))}
      (dep ↓↑) (splitl (ap-[]₁ [id]T refl))))
      (dep (inj-↑[p#] (undep (transᴰ (transᴰ (transᴰ (dep (sym ↓[p#]))
      (ap-[]₁ (sym (trans (ap-[]T₁ [id]T) (pA .witness))) (movel ↓↑))) (symᴰ [∘])) (pt .witness))))))
    nn-ctors .↑ᴰ {Γᴰ = (↑↑ , iΓ , pΓ)} {Aᴰ = (iA , pA)} (it , pt)
      = by (ap-[] (iΓ .witness) (iΓ .witness) (iA .witness) (ap-id (iΓ .witness)) (it .witness))
      , by (transᴰ [∘] (transᴰ (ap-[] refl refl (dep (trans (ap-[]T₁ [id]T) (pA .witness))) reflᴰ
      (transᴰ (ap-[]₁ [id]T [id]) (pt .witness))) (symᴰ (dep ↓*↑))))
    nn-ctors .↓[]ᴰ = refl
    nn-ctors .↑↓ᴰ = refl
    nn-ctors .↓↑ᴰ = refl

  nn : CwFwEᴰ syn
  nn .sortsᴰ = nn-sorts
  nn .coreᴰ = nn-ctors
  nn .Π-strᴰ = {!!}
  nn .U-strᴰ = {!!}

  opaque
    unfolding ↓*ᴰ nn-ctors

    -- Final induction over contexts to show that ↑↑ is the identity if all the
    -- bindings are zero.
    ⟦↑↑⟧≡↑↑ : {Γ : Con}
      → (let (↑↑Γ , _ , _) = CwFwE-elim.⟦_⟧ᶜ nn Γ)
      → (let (↑↑⟦Γ⟧ , _ , _) = CwFwE-elim.⟦_⟧ᶜ nn ⟦ Γ ⟧ᶜ)
      → ⟦ ↑↑Γ ⟧ˢ ≡ ↑↑⟦Γ⟧
    ⟦↑↑⟧≡↑↑ {Γ} = (CwFwE-elim-Con.⟦_⟧
      (λ Γ
        → (let (↑↑Γ , _ , _) = CwFwE-elim.⟦_⟧ᶜ nn Γ)
        → (let (↑↑⟦Γ⟧ , _ , _) = CwFwE-elim.⟦_⟧ᶜ nn ⟦ Γ ⟧ᶜ)
        → (⟦ ↑↑Γ ⟧ˢ ≡ ↑↑⟦Γ⟧) true)
        (by refl)
        (λ Γ A pr →
          let (↑↑Γ , _ , _) = CwFwE-elim.⟦_⟧ᶜ nn Γ in
          let (↑↑⟦Γ⟧ , _ , _) = CwFwE-elim.⟦_⟧ᶜ nn ⟦ Γ ⟧ᶜ in
          let ( _ , pA) = CwFwE-elim.⟦_⟧ᵀ nn ⟦ A ⟧ᵀ in
          by (undep (ap-,, refl refl (dep (cong (_∘ p) (pr .witness))) reflᴰ (splitl refl))))
        (λ Γ A pr →
          let (↑↑Γ , _ , _) = CwFwE-elim.⟦_⟧ᶜ nn Γ in
          let (↑↑⟦Γ⟧ , _ , _) = CwFwE-elim.⟦_⟧ᶜ nn ⟦ Γ ⟧ᶜ in
          let ( _ , pA) = CwFwE-elim.⟦_⟧ᵀ nn ⟦ A ⟧ᵀ in
          by (undep (ap-,, refl refl (dep (cong (_∘ p) (pr .witness))) reflᴰ (splitr (splitl (splitl [id]))))))
        ( λ Γ pr → by (trans ∘id (pr .witness)) ) Γ) .witness

    -- Main theorems:

    types-need-nothing : Ty Γ ≃ Ty ⟦ Γ ⟧ᶜ
    types-need-nothing .to = ⟦_⟧ᵀ
    types-need-nothing {Γ = Γ} .from A =
      let (↑↑ , iΓ , pΓ) = CwFwE-elim.⟦_⟧ᶜ nn Γ in
      let (iA , pA) = CwFwE-elim.⟦_⟧ᵀ nn A in (A [ ↑↑ ]T)
    types-need-nothing {Γ = Γ} .to-from A =
      let (↑↑ , iΓ , pΓ) = CwFwE-elim.⟦_⟧ᶜ nn Γ in
      let (iA , pA) = CwFwE-elim.⟦_⟧ᵀ nn A in
      let (i↑↑ , p↑↑) =  CwFwE-elim.⟦_⟧ˢ nn ↑↑ in
      trans (ap-[]T₀ ⟦↑↑⟧≡↑↑) (pA .witness)  
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
    erased-terms-need-nothing {Γ = Γ} {A = A} .to-from a =
      let (↑↑ , iΓ , pΓ) = CwFwE-elim.⟦_⟧ᶜ nn Γ in
      let (ia , pa) = CwFwE-elim.⟦_⟧ᵗ nn a in
      let (i↑↑ , p↑↑) =  CwFwE-elim.⟦_⟧ˢ nn ↑↑ in
      transᴰ {p = ap-Tm (ap-[]T₀ ⟦↑↑⟧≡↑↑)} (ap-[]₀ ⟦↑↑⟧≡↑↑) (pa .witness)  
    erased-terms-need-nothing {Γ = Γ} .from-to a =
      let (ia , pa) = CwFwE-elim.⟦_⟧ᵗ nn a in pa .witness
