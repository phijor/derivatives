{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Derivative.Indexed.Mu where

open import Derivative.Indexed.Container
open import Derivative.Indexed.Derivative
open import Derivative.Indexed.ChainRule

open import Derivative.Prelude
open import Derivative.Decidable
open import Derivative.Isolated
open import Derivative.Maybe
open import Derivative.Sum
open import Derivative.W

open import Cubical.Data.Sigma
import      Cubical.Data.Unit as Unit
open import Cubical.Functions.FunExtEquiv

private
  variable
    ℓ : Level
    Ix : Type ℓ

open Container

μ : (F : Container ℓ (Maybe Ix)) → Container ℓ Ix
μ {ℓ} {Ix} F = shape ◁ pos module μ where
  open Container F renaming (Shape to S ; Pos to P)

  shape : Type ℓ
  shape = W S (P nothing)

  pos : Ix → shape → Type ℓ
  pos ix = Wᴰ S (P nothing) (P (just ix))

module _ (F : Container ℓ (Maybe Ix)) where
  open Container F renaming (Shape to S ; Pos to P)
  
  μ-in-equiv : Equiv (F [ μ F ]) (μ F)
  μ-in-equiv = [ shape ◁≃ pos ] where
    shape : Shape (F [ μ F ]) ≃ Shape (μ F)
    shape = W-in-equiv

    pos : ∀ ix w* → Pos (μ F) ix (W-in w*) ≃ Pos (F [ μ F ]) ix w*
    pos ix (s , ws) = Wᴰ-out-equiv S (P nothing) (P (just ix)) s ws

  μ-in : F [ μ F ] ⊸ μ F
  μ-in = Equiv.as-⊸ μ-in-equiv

  μ-out-equiv : Equiv (μ F) (F [ μ F ])
  μ-out-equiv = [ shape ◁≃ pos ] where
    shape : Shape (μ F) ≃ Shape (F [ μ F ])
    shape = W-out-equiv

    pos : ∀ ix s* → Pos (F [ μ F ]) ix (W-out s*) ≃ Pos (μ F) ix s*
    pos ix (sup s f) = Wᴰ-in-equiv _ _ _ s f

  μ-out : μ F ⊸ F [ μ F ]
  μ-out = Equiv.as-⊸ μ-out-equiv

  μ-rec : (G : Container ℓ Ix)
    → (F [ G ]) ⊸ G
    → μ F ⊸ G
  μ-rec G φ = [ shape ⊸ pos ] module μ-rec where
    open Container G renaming (Shape to T ; Pos to Q)

    module φ = _⊸_ φ

    shape : W S (P ₁) → T
    shape (sup s f) = φ.shape (s , λ p → shape (f p))

    shape-β : shape ≡ φ.shape ∘ Σ-map-snd (λ s (f : P ₁ s → W S _) → shape ∘ f) ∘ W-out
    shape-β = funExt λ { (sup s f) → refl }

    pos-fun : ∀ i → (s : W S (P ₁)) → Q i (shape s) → Pos (μ F) i s
    pos-fun i (sup s f) =
      Q i (φ.shape (s , shape ∘ f))
        →⟨ equivFun $ φ.pos i (s , shape ∘ f) ⟩
      (P (just i) s ⊎ (Σ[ p ∈ P nothing s ] Q i (shape (f p))))
        →⟨ ⊎-map-right (Σ-map-snd $ pos-fun i ∘ f) ⟩
      (P (just i) s ⊎ (Σ[ p ∈ P nothing s ] Pos (μ F) i (f p)))
        →⟨ Wᴰ-in S (P nothing) (P (just i)) s f ⟩
      Wᴰ S (P nothing) (P (just i)) (sup s f)
        →∎

    is-equiv-pos-fun : ∀ i (w : W S (P ₁)) → isEquiv (pos-fun i w)
    is-equiv-pos-fun i (sup s f) = goal where
      step-1 : isEquiv (⊎-map-right {A = P (just i) s} (Σ-map-snd $ pos-fun i ∘ f))
      step-1 = isEquiv→isEquiv-⊎-map-right $ isEquiv-Σ-map-snd $ is-equiv-pos-fun i ∘ f

      step-2 : isEquiv (Wᴰ-in _ _ _ s f ∘ ⊎-map-right (Σ-map-snd $ pos-fun i ∘ f))
      step-2 = isEquiv-∘ (isEquiv-Wᴰ-in _ _ _ s f) step-1

      goal : isEquiv (Wᴰ-in _ _ _ s f ∘ ⊎-map-right (Σ-map-snd $ pos-fun i ∘ f) ∘ equivFun (φ.pos i (s , shape ∘ f)))
      goal = isEquiv-∘ step-2 (equivIsEquiv (φ.pos i _))

    pos' : ∀ i → (s : W S (P ₁)) → Q i (shape s) ≃ Pos (μ F) i s
    pos' i w .fst = pos-fun i w
    pos' i w .snd = is-equiv-pos-fun i w

    pos : ∀ i → (s : W S (P ₁)) → Q i (shape s) ≃ Pos (μ F) i s
    pos i (sup s f) =
      Q i (φ.shape (s , shape ∘ f))
        ≃⟨ φ.pos i (s , shape ∘ f) ⟩
      (P (just i) s ⊎ (Σ[ p ∈ P nothing s ] Q i (shape (f p))))
        ≃⟨ ⊎-right-≃ (Σ-cong-equiv-snd λ p → pos i (f p)) ⟩
      (P (just i) s ⊎ (Σ[ p ∈ P nothing s ] Pos (μ F) i (f p)))
        ≃⟨ Wᴰ-in-equiv S (P nothing) (P (just i)) s f ⟩
      Wᴰ S (P nothing) (P (just i)) (sup s f)
        ≃∎

  μ-rec-β' : (G : Container ℓ Ix)
    → (α : (F [ G ]) ⊸ G)
    → μ-rec G α ≡ μ-out ⋆ [-]-map F (μ-rec G α) ⋆ α
  μ-rec-β' G α = ⊸≡-ext (μ-rec.shape-β G α) λ where
    ix (sup s f) → refl

  μ-rec-β : (G : Container ℓ Ix)
    → (α : (F [ G ]) ⊸ G)
    → μ-in ⋆ μ-rec G α ≡ [-]-map F (μ-rec G α) ⋆ α
  μ-rec-β G α = ⊸≡-ext refl λ ix s → {! !}

  μ-rec-unique' : (G : Container ℓ Ix)
    → (α : (F [ G ]) ⊸ G)
    → isContr (Σ[ α* ∈ μ F ⊸ G ] α* ≡ μ-out ⋆ [-]-map F α* ⋆ α )
  μ-rec-unique' G α .fst .fst = μ-rec G α
  μ-rec-unique' G α .fst .snd = μ-rec-β' G α
  μ-rec-unique' G α .snd (ζ , ζ-β) = ΣPathP (goal , {! !}) where
    module α = _⊸_ α
    module ζ = _⊸_ ζ

    shape-≡-ext : ∀ w → μ-rec.shape G α w ≡ ζ.shape w
    shape-≡-ext (sup s f) = p ∙ q
      module shape-≡-ext where
        p = cong α.shape (ΣPathP (refl′ s , funExt (shape-≡-ext ∘ f)))
        q = sym $ cong _⊸_.shape ζ-β ≡$ sup s f

        filler = compPath-filler p q

    shape-≡ : μ-rec.shape G α ≡ ζ.shape
    shape-≡ = funExt shape-≡-ext

  {-
    pos-≡' : ∀ ix (s : S) (f : _)
      → PathP (λ i → Pos G ix (shape-≡-ext (sup s f) i) → μ.pos F ix (sup s f)) (equivFun (μ-rec.pos G α ix (sup s f))) (equivFun $ ζ.pos ix (sup s f))
    pos-≡' ix s f = compPathP' {B = B} {p = p} {q = q} pᴰ qᴰ
      module pos-≡' where
        B : Shape G → Type _
        B t = Pos G ix t → μ.pos F ix (sup s f)

        p = cong α.shape (ΣPathP (refl , funExt (shape-≡-ext ∘ f)))
        q = sym $ cong _⊸_.shape ζ-β ≡$ sup s f

        pᴰ : PathP (λ i → Pos G ix (shape-≡-ext.p s f i) → μ.pos F ix (sup s f))
          (Wᴰ-in _ _ _ s f ∘ ⊎-map-right (Σ-map-snd λ { p → μ-rec.pos-fun G α ix (f p) }) ∘ equivFun (α.pos ix (s , μ-rec.shape _ _ ∘ f)))
          (Wᴰ-in _ _ _ s f ∘ ⊎-map-right (Σ-map-snd λ { p → equivFun (ζ.pos ix (f p)) }) ∘ equivFun (α.pos ix (s , ζ.shape ∘ f)))
        pᴰ i = Wᴰ-in _ _ _ s f ∘ {! !}

        qᴰ : PathP (λ i → Pos G ix (shape-≡-ext.q s f i) → μ.pos F ix (sup s f))
          (Wᴰ-in _ _ _ s f ∘ ⊎-map-right (Σ-map-snd λ { p → equivFun (ζ.pos ix (f p)) }) ∘ equivFun (α.pos ix (s , ζ.shape ∘ f)))
          (equivFun (ζ.pos ix (sup s f)))
        qᴰ i = equivFun (ζ-β (~ i) ._⊸_.pos ix (sup s f))

        filler = compPathP'-filler {B = B} {p = p} {q = q} pᴰ qᴰ
    -}

    pos-≡ : ∀ ix (w : W S (P ₁)) → PathP (λ i → Pos G ix (shape-≡ i w) ≃ μ.pos F ix w) (μ-rec.pos G α ix w) (ζ.pos ix w)
    pos-≡ ix (sup s f) = compPathP' {B = B} {p = p} {q = q} pᴰ qᴰ
      module pos-≡ where
        B : Shape G → Type _
        B t = Pos G ix t ≃ μ.pos F ix (sup s f)

        open shape-≡-ext s f using (p ; q)

        yᴰ : _ ≃ _
        yᴰ = α.pos ix (s , ζ.shape ∘ f) ∙ₑ ⊎-right-≃ (Σ-cong-equiv-snd (ζ.pos ix ∘ f)) ∙ₑ Wᴰ-in-equiv _ _ _ s f

        pᴰ : PathP (λ i → B (shape-≡-ext.p s f i)) (μ-rec.pos G α ix (sup s f)) yᴰ
        -- pᴰ = equivPathP $ funExtNonDep λ {x₀} {x₁} h → cong (Wᴰ-in _ _ _ s f) λ where
        --   i → ⊎-map-right (Σ-map-snd λ { p → {! !} }) $ equivFun (α.pos ix (s , λ p₁ → {! q !})) {!h!} -- (equivFun {! !} (α.pos ix (s , ?)))
        pᴰ = {! !}
          -- equivPathP $ λ where
          --   i q → Wᴰ-in _ _ _ s f (⊎-map-right (λ xx → {! !}) {! !})
          -- $ {!cong₂ (λ x y → ⊎-map-right (equivFun (Σ-cong-equiv-snd (λ p → x ix (f p)) ()) !}

        qᴰ : PathP (λ i → B (shape-≡-ext.q s f i)) yᴰ (ζ.pos ix (sup s f))
        qᴰ i = ζ-β (~ i) ._⊸_.pos ix (sup s f)

    goal : μ-rec G α ≡ ζ
    goal = ⊸≡ shape-≡ $ funExt₂ pos-≡

    goal-coh : PathP (λ i → goal i ≡ μ-out ⋆ [-]-map F (goal i) ⋆ α) (μ-rec-β' G α) ζ-β
    goal-coh i j ._⊸_.shape (sup s f) = shape-≡-ext.filler s f (~ j) i
    goal-coh i j ._⊸_.pos ix (sup s f) = {! pos-≡.filler ix s f  !}

  μ-rec-unique : (G : Container ℓ Ix)
    → (α : (F [ G ]) ⊸ G)
    → isContr (Σ[ α* ∈ μ F ⊸ G ] μ-in ⋆ α* ≡ [-]-map F α* ⋆ α )
  μ-rec-unique G α .fst .fst = μ-rec G α
  μ-rec-unique G α .fst .snd = μ-rec-β G α
  μ-rec-unique G α .snd (α* , p) = ΣPathP ({! !} , {! !})

  isEquivFrom-μ-rec : (G : Container ℓ Ix)
    → (φ : (F [ G ]) ⊸ G)
    → isContainerEquiv (μ-rec G φ)
    → isContainerEquiv φ
  isEquivFrom-μ-rec G φ is-equiv-μ-rec = is-equiv-φ where
    is-equiv-comp : isContainerEquiv (μ-out ⋆ [-]-map F (μ-rec G φ) ⋆ φ)
    is-equiv-comp = subst isContainerEquiv (μ-rec-β' G φ) is-equiv-μ-rec

    is-equiv-μ-out⋆F[μ-rec] : isContainerEquiv (μ-out ⋆ [-]-map F (μ-rec G φ))
    is-equiv-μ-out⋆F[μ-rec] = isContainerEquivComp
      μ-out
      ([-]-map F (μ-rec G φ))
      (equivIsContainerEquiv μ-out-equiv)
      (isEquiv-[-]-map F (μ-rec G φ) is-equiv-μ-rec)

    is-equiv-φ : isContainerEquiv φ
    is-equiv-φ = isContainerEquivCompRight' (μ-out ⋆ [-]-map F (μ-rec G φ)) φ is-equiv-μ-out⋆F[μ-rec] is-equiv-comp

μ-rule : ∀ (F : Container _ 𝟚) →
  μ ((↑ (∂ ₀° F [ μ F ])) ⊕ ((↑ (∂ ₁° F [ μ F ])) ⊗ π₁))
    ⊸
  ∂ tt° (μ F)
μ-rule F = μ-rec G (∂ tt° (μ F)) α module μ-rule where
  open Container F renaming (Shape to S ; Pos to P)

  G : Container _ 𝟚
  G = (↑ (∂ ₀° F [ μ F ])) ⊕ ((↑ (∂ ₁° F [ μ F ])) ⊗ π₁)

  G[_] : Container _ 𝟙 → Container _ 𝟙
  G[ Y ] = (∂ ₀° F [ μ F ]) ⊕ ((∂ ₁° F [ μ F ]) ⊗ Y)

  G-subst : ∀ Y → Equiv (G [ Y ]) (G[ Y ])
  G-subst Y = [ shape ◁≃ pos ] where
    shape-Iso : Iso (Shape (G [ Y ])) (Shape G[ Y ])
    shape-Iso .Iso.fun (inl s , _) = inl s
    shape-Iso .Iso.fun (inr (s , _) , f) = inr (s , f (inr •))
    shape-Iso .Iso.inv (inl s) = inl s , λ ()
    shape-Iso .Iso.inv (inr (s , y)) = inr (s , •) , λ { (inr •) → y }
    shape-Iso .Iso.rightInv (inl s) = refl
    shape-Iso .Iso.rightInv (inr (s , y)) = refl
    shape-Iso .Iso.leftInv (inl s , 0→Y) = ΣPathP (refl , λ { i () })
    shape-Iso .Iso.leftInv (inr (s , •) , f) = ΣPathP (refl , funExt λ { (inr •) → refl′ (f _) })

    shape = isoToEquiv shape-Iso

    μP : W S (P ₁) → Type
    μP = Wᴰ S (P ₁) (P ₀)

    pos₀ : (s : S) (p° : P ₀ s °) (f₁ : P ₁ s → W S (P ₁)) (f₀ : 𝟘* → Shape Y)
      →
        (P ₀ s - p°) ⊎ (Σ[ p ∈ P ₁ s ] μP (f₁ p))
          ≃
        ((P ₀ s - p°) ⊎ (Σ[ p ∈ P ₁ s ] μP (f₁ p))) ⊎ (Σ[ x ∈ 𝟘* ] Pos Y _ (f₀ x))
    pos₀ _ _ _ _ = ⊎-empty-right (λ ())

    pos₁ : (s : S) (p° : P ₁ s °) (f₁ : (P ₁ s - p°) → W S (P ₁)) (f₀ : 𝟘* ⊎ 𝟙 → Shape Y)
      → (P ₀ s ⊎ (Σ[ p ∈ (P ₁ s) - p° ] μP (f₁ p))) ⊎ (Pos Y _ (f₀ (inr •)))
          ≃
        ((P ₀ s ⊎ (Σ[ p ∈ (P ₁ s) - p° ] μP (f₁ p))) ⊎ 𝟘) ⊎ (Σ[ i ∈ 𝟘* ⊎ 𝟙 ] Pos Y _ (f₀ i))
    pos₁ s p° f₁ f₀ =
      let X = P ₀ s
          W = (Σ[ p ∈ (P ₁ s) - p° ] μP (f₁ p))
          Z : 𝟘* ⊎ 𝟙 → Type _
          Z i = Pos Y _ (f₀ i)
      in
      (X ⊎ W) ⊎ (Z (inr •))
        ≃⟨ ⊎-left-≃ (⊎-empty-right λ ()) ⟩
      ((X ⊎ W) ⊎ 𝟘) ⊎ (Z (inr •))
        ≃⟨ ⊎-right-≃ $ invEquiv (Σ-contractFst (isOfHLevelRespectEquiv 0 (⊎-empty-left λ ()) Unit.isContrUnit)) ⟩
      ((X ⊎ W) ⊎ 𝟘) ⊎ (Σ[ i ∈ 𝟘* ⊎ 𝟙 ] Z i)
        ≃∎

    pos : (i : 𝟙) → (s : Shape $ G [ Y ]) → Pos G[ Y ] i (equivFun shape s) ≃ Pos (G [ Y ]) i s
    pos • (inl ((s , p°) , f₁) , f₀) = pos₀ s p° f₁ f₀
    pos • (inr (((s , p°) , f₁) , •) , f₀) = pos₁ s p° f₁ f₀

  η₀ : (G [ ∂ tt° (μ F) ]) ⧟ ((∂ ₀° F [ μ F ]) ⊕ ((∂ ₁° F [ μ F ]) ⊗ ∂ tt° (μ F)))
  η₀ = G-subst (∂ tt° (μ F))

  η₁ : ∂ tt° (F [ μ F ]) ⧟ ∂ tt° (μ F)
  η₁ = ∂-map-equiv tt° (μ-in-equiv F)

  α : (G [ ∂ tt° (μ F) ]) ⊸ ∂ tt° (μ F)
  α =
    (G [ ∂ tt° (μ F) ])
      ⧟⟨ η₀ ⟩
    ((∂ ₀° F [ μ F ]) ⊕ ((∂ ₁° F [ μ F ]) ⊗ ∂ tt° (μ F)))
      ⊸⟨ binary-chain-rule F (μ F) ⟩
    ∂ tt° (F [ μ F ])
      ⧟⟨ η₁ ⟩
    ∂ tt° (μ F)
      ⊸∎

μ-discrete : (F : Container _ 𝟚)
  → (∀ ix s → Discrete (Pos F ix s))
  → (∀ w → Discrete (Pos (μ F) • w))
μ-discrete F discrete-P = discrete-Wᴰ S (P ₁) (P ₀) (discrete-P ₁) (discrete-P ₀) where
  open Container F renaming (Shape to S ; Pos to P)

Discrete→isEquiv-μ-chain-rule : (F : Container _ 𝟚) → (∀ ix s → Discrete (Pos F ix s)) → isContainerEquiv (binary-chain-rule F (μ F))
Discrete→isEquiv-μ-chain-rule F discrete-P = DiscreteContainer→isEquivBinaryChainRule F (μ F) (discrete-P ₁) (μ-discrete F discrete-P)

module _ (F : Container _ 𝟚) (is-equiv-chain-rule : isContainerEquiv (binary-chain-rule F (μ F))) where
  open Container F renaming (Shape to S ; Pos to P)
  open μ-rule F
  private
    module α = _⊸_ α

    is-equiv-Σ-isolate : ∀ (s : S) (f : P ₁ s → W S (P ₁)) → isEquiv (Σ-isolate (P ₁ s) (Wᴰ S (P ₁) (P ₀) ∘ f))
    is-equiv-Σ-isolate = isEquivBinaryChainRule→isEquiv-Σ-isolate F (μ F) is-equiv-chain-rule

  μ-rule-shape : Shape (μ G) → Shape ((∂ tt° (μ F)))
  μ-rule-shape = W-elim λ where
    (inl ((s , p₀) , f)) _ rec → sup s f , top (p₀ .fst) , isIsolatedTop (p₀ .snd)
    (inr (((s , p₁) , f) , _)) _ rec →
      let (w , wᴰ) = rec (inr •)
      in sup s (stitch p₁ (f , w))
        , below (p₁ .fst) (subst (Pos (μ F) •) (sym (stitch-β p₁ f {w})) (wᴰ .fst))
        , isIsolatedBelow (isIsolatedΣ (p₁ .snd) (isIsolatedSubst (Pos (μ F) •) (sym (stitch-β p₁ f {w})) (wᴰ .snd)))

  μ-rule-shape⁻¹ : Shape ((∂ tt° (μ F))) → Shape (μ G)
  μ-rule-shape⁻¹ = uncurry $ W-elim λ where
    s f rec (top p₀ , isolated-top-p₀) → sup (inl ((s , (p₀ , isIsolatedFromTop isolated-top-p₀)) , f)) λ ()
    s f rec (below p₁ wᴰ , isolated-below-p₁-wᴰ) →
      let (isolated-p₁ , isolated-wᴰ) = isEquiv-Σ-isolate→isIsolatedPair (is-equiv-Σ-isolate s f) (isIsolatedFromBelow isolated-below-p₁-wᴰ)
      in sup (inr (((s , p₁ , isolated-p₁) , f ∘ fst) , •)) λ where
        (inr •) → rec p₁ (wᴰ , isolated-wᴰ)

  μ-rule-shape-rinv : section μ-rule-shape μ-rule-shape⁻¹
  μ-rule-shape-rinv (sup s f , top p₀ , _) = ΣPathP (refl , Isolated≡ refl)
  μ-rule-shape-rinv (sup s f , below p₁ wᴰ , _) = ΣPathP (cong (sup s) {! !} , IsolatedPathP {! !})

  μ-rule-shape-linv : retract μ-rule-shape μ-rule-shape⁻¹
  μ-rule-shape-linv (sup (inl ((s , p₀ , _) , f)) g) = cong₂ sup (cong inl (ΣPathP (cong (s ,_) (Isolated≡ (refl′ p₀)) , refl′ f))) $ funExt λ ()
  μ-rule-shape-linv (sup (inr (((s , p₁) , f) , _)) g) = cong₂ sup (cong inr {! !}) {! !}

  μ-rule-shape-Iso : Iso (Shape (μ G)) (Shape ((∂ tt° (μ F))))
  μ-rule-shape-Iso .Iso.fun = μ-rule-shape
  μ-rule-shape-Iso .Iso.inv = μ-rule-shape⁻¹
  μ-rule-shape-Iso .Iso.rightInv = μ-rule-shape-rinv
  μ-rule-shape-Iso .Iso.leftInv = μ-rule-shape-linv

  μ-rule⁻¹ : isEquiv (μ-rec.shape G (∂ tt° (μ F)) α)
  μ-rule⁻¹ .equiv-proof = uncurry contr-fib where
    contr-fib : (w : W S (P ₁)) (wᴰ : Wᴰ S (P ₁) (P ₀) w °) → isContr (fiber (μ-rec.shape G _ α) (w , wᴰ))
    contr-fib (sup s f) (top p₀ , isolated-top-p₀) = {! !} where
      top-equiv : {! !} ≃ fiber (μ-rec.shape G _ α) ((sup s f) , (top p₀ , isolated-top-p₀))
      top-equiv =
        {! !}
          ≃⟨ {! !} ⟩
        -- Σ[ x ∈ Σ (Shape G) (λ t → Pos G ₁ t → W (Shape G) (Pos G ₁)) ] (α.shape (x .fst , λ p → μ-rec.shape _ _ α (x .snd p))) ≡ ((sup s f) , (top p₀ , isolated-top-p₀))
        --   ≃⟨⟩
        Σ[ x ∈ Σ (Shape G) (λ t → Pos G ₁ t → W (Shape G) (Pos G ₁)) ] μ-rec.shape G _ α (sup (x .fst) (x .snd)) ≡ ((sup s f) , (top p₀ , isolated-top-p₀))
          ≃⟨ Σ-cong-equiv W-in-equiv {! !} ⟩
        Σ[ x ∈ W (Shape G) (Pos G ₁) ] μ-rec.shape G _ α x ≡ ((sup s f) , (top p₀ , isolated-top-p₀))
          ≃∎
    contr-fib (sup s f) (below p₁ wᴰ , isolated-below-p₁-wᴰ) = {! !}

  isEquiv-μ-rule : isContainerEquiv (μ-rule F)
  isEquiv-μ-rule = μ-rule⁻¹

{-
module _ (F : Container _ 𝟚) where
  open Container F renaming (Shape to S ; Pos to P)
  open μ-rule F

  -- TODO: Prove that having a strong chain rule for F[μF] implies that μ-rule F is strong.
  isEquiv-ind→isEquiv-μ-rule : isContainerEquiv (μ-rule.α F) → isContainerEquiv (μ-rule F)
  isEquiv-ind→isEquiv-μ-rule is-equiv-α = isoToIsEquiv iso where
    module α = Equiv (isContainerEquiv→Equiv α is-equiv-α)

    is-equiv-chain-rule : isContainerEquiv (binary-chain-rule F (μ F))
    is-equiv-chain-rule = {! !}
    
    is-equiv-Σ-isolate : ∀ (s : S) (f : P ₁ s → W S (P ₁)) → isEquiv (Σ-isolate (P ₁ s) (Wᴰ S (P ₁) (P ₀) ∘ f))
    is-equiv-Σ-isolate = isEquivBinaryChainRule→isEquiv-Σ-isolate F (μ F) is-equiv-chain-rule

    isolate-below-pair : ∀ (s : S) (f : P ₁ s → W S (P ₁)) {p₁ : P ₁ s} {wᴰ : Wᴰ S (P ₁) (P ₀) (f p₁)}
      → isIsolated (p₁ , wᴰ)
      → isIsolated p₁ × isIsolated wᴰ
    isolate-below-pair s f = isEquiv-Σ-isolate→isIsolatedPair (is-equiv-Σ-isolate s f)

    inv : Shape (∂ tt° (μ F)) → Shape (μ G)
    inv = uncurry $ W-elim λ where
      s f invᴿ (top p₀ , isolated-top-p₀) → sup (inl ((s , p₀ , isIsolatedFromTop isolated-top-p₀) , f)) λ ()
      s f invᴿ (below p₁ wᴰ , isolated-below-p₁-wᴰ) →
        let (isolated-p₁ , isolated-wᴰ) = isolate-below-pair s f (isIsolatedFromBelow isolated-below-p₁-wᴰ)
        in
        sup (inr (((s , p₁ , isolated-p₁) , f ∘ fst) , •)) λ where
          (inr •) → invᴿ p₁ (wᴰ , isolated-wᴰ)

    rinv : ∀ y → μ-rec.shape G (∂ tt° (μ F)) α (inv y) ≡ y
    rinv (sup s f , top p₀ , isolated-top-p₀) = ΣPathP (refl′ (sup s f) , Isolated≡ (refl′ (top p₀)))
    rinv (sup s f , below p₁ wᴰ , isolated-below-p₁-wᴰ) =
      ΣPathP (cong (sup s) lemma , {! !}) -- ΣPathP (cong (sup s) lemma , {! IsolatedPathP {B = Pos (μ F) •} {p = cong (sup s) lemma} {! !} !})
      where
        isolated-p₁ : isIsolated p₁
        isolated-p₁ = isolate-below-pair s f {wᴰ = wᴰ} (isIsolatedFromBelow isolated-below-p₁-wᴰ) .fst

        lemma-ext : (p₁ : P ₁ s) → _ ≡ f p₁
        lemma-ext p₁ = {! !}

        lemma : _ ≡ f
        lemma = funExt lemma-ext
        -- lemma = stitch-eval (p₁ , isolated-p₁) f {!_!} ?

    iso : Iso (Shape (μ G)) (Shape (∂ tt° (μ F)))
    iso .Iso.fun = μ-rec.shape G (∂ tt° (μ F)) α
    iso .Iso.inv = inv
    iso .Iso.rightInv = rinv
    iso .Iso.leftInv xx = {! !}
-}

module isEquiv-μ-rule (F : Container _ 𝟚) (is-equiv-μ-rule : isContainerEquiv (μ-rule F)) where
  open Container F renaming (Shape to S ; Pos to P)
  open μ-rule F using (α ; G ; η₀ ; η₁)

  private
    μP = Wᴰ (Shape F) (Pos F ₁) (Pos F ₀)


    is-equiv-α : isContainerEquiv α
    is-equiv-α = isEquivFrom-μ-rec G (∂ tt° (μ F)) α is-equiv-μ-rule

  is-equiv-chain-rule : isContainerEquiv (binary-chain-rule F (μ F))
  is-equiv-chain-rule = isContainerEquivCompLeftRight η₀ η₁ (binary-chain-rule F (μ F)) {! is-equiv-α !}
  
  isEquiv-Σ-isolate : ∀ (s : S) (f : P ₁ s → W S (P ₁)) → isEquiv (Σ-isolate (P ₁ s) (μP ∘ f))
  isEquiv-Σ-isolate = isEquivBinaryChainRule→isEquiv-Σ-isolate F (μ F) is-equiv-chain-rule

  foo : (w : W S (P ₁)) → isEquiv (Σ-isolate (P ₁ (W-shape w)) (μP ∘ W-branch w))
  foo (sup s f) = isEquiv-Σ-isolate s f

  isEquiv-μ-rule→IsolatedEquiv : ∀ (s : S) (f : P ₁ s → W S (P ₁))
    →
      μP (sup s f) °
        ≃
      (P ₀ s °) ⊎ (Σ[ (p , _) ∈ P ₁ s ° ] (μP (f p) °))
  isEquiv-μ-rule→IsolatedEquiv s f =
    μP (sup s f) °
      ≃⟨ IsolatedSubstEquiv (Wᴰ-out-equiv _ _ _ s f) ⟩
    ((Pos F ₀ s) ⊎ (Σ[ p ∈ Pos F ₁ s ] μP (f p))) °
      ≃⟨ IsolatedSumEquiv ⟩
    (Pos F ₀ s °) ⊎ ((Σ[ p ∈ Pos F ₁ s ] μP (f p)) °)
      ≃⟨ ⊎-right-≃ $ invEquiv (_ , isEquiv-Σ-isolate s f) ⟩
    (Pos F ₀ s °) ⊎ (Σ[ (p , _) ∈ Pos F ₁ s ° ] (μP (f p) °))
      ≃∎

  discrete-μP : ∀ w → Discrete (Wᴰ S (P ₁) (P ₀) w)
  discrete-μP (sup s f) (top p₀) = {! isIsolatedFromTop !}
  discrete-μP (sup s f) (below p₁ wᴰ) = {! !}

  discrete-P₁ : ∀ s → Discrete (P ₁ s)
  discrete-P₁ s = {! !}
