{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Derivative.Indexed.MuRule where

open import Derivative.Indexed.Container
open import Derivative.Indexed.Mu
open import Derivative.Indexed.Derivative
open import Derivative.Indexed.ChainRule

open import Derivative.Prelude
open import Derivative.Decidable
open import Derivative.Embedding
open import Derivative.Isolated
open import Derivative.Maybe
open import Derivative.Remove
open import Derivative.Sum
open import Derivative.W

open import Cubical.Foundations.Path
import      Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
import      Cubical.Data.Unit as Unit
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding

private
  variable
    ℓ : Level
    Ix : Type ℓ

open Container
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

{-
module _ (F : Container _ 𝟚) where
  open μ-rule F

  -- μ-rule-init' : (H : Container _ 𝟙) (β : G [ H ] ⊸ H) → isProp (Σ[ ρ ∈ ∂ tt° (F [ μ F ]) ⊸ H ] binary-chain-rule F (μ F) ⋆ ρ ≡ [-]-map G ρ ⋆ β)
  -- μ-rule-init' H β = {! !}

  μ-rule-init : (H : Container _ 𝟙) (β : G [ H ] ⊸ H) → isProp (Σ[ ρ ∈ ∂ tt° (μ F) ⊸ H ] α ⋆ ρ ≡ [-]-map G ρ ⋆ β)
  μ-rule-init H β (ρ₀ , comm₀) (ρ₁ , comm₁) = goal where
    ρ-path : ρ₀ ≡ ρ₁
    ρ-path = ⊸≡ {! ρ₀ ._⊸_.shape !} {! !}

    goal : (ρ₀ , comm₀) ≡ (ρ₁ , comm₁)
    goal = ΣPathP (ρ-path , {! !})

  μ-rule-init' : (H : Container _ 𝟙) (β : G [ H ] ⊸ H) → isContr (Σ[ β* ∈ ∂ tt° (μ F) ⊸ H ] α ⋆ β* ≡ [-]-map G β* ⋆ β)
  μ-rule-init' H β .fst = β* , ? where
    foo : ∂ tt° (μ F) ⊸ G [ H ]
    foo ._⊸_.shape = uncurry $ W-elim λ where
      s f rec (top p₀ , isolated-top-p₀) → inl ((s , p₀ , ?) , f) , λ ()
      s f rec (below p₁ wᴰ , _) → inr (((s , p₁ , {! !}) , {!f!}) , •) , λ { (inr •) → rec p₁ (wᴰ , {! !}) .snd {!f!} }
    foo ._⊸_.pos = {! !}

    β* : ∂ tt° (μ F) ⊸ H
    β* = foo ⋆ β
  μ-rule-init' H β .snd = {! !}
-}

module _ (F : Container _ 𝟚) (is-equiv-chain-rule : isContainerEquiv (binary-chain-rule F (μ F))) where
  open Container F renaming (Shape to S ; Pos to P)
  open μ-rule F
  private
    module α = _⊸_ α

    is-equiv-Σ-isolate : ∀ (s : S) (f : P ₁ s → W S (P ₁)) → isEquiv (Σ-isolate (P ₁ s) (Wᴰ S (P ₁) (P ₀) ∘ f))
    is-equiv-Σ-isolate = isEquivBinaryChainRule→isEquiv-Σ-isolate F (μ F) is-equiv-chain-rule

    Σ-isolate-equiv : ∀ (s : S) (f : P ₁ s → W S (P ₁)) → (Σ[ (p , _) ∈ Pos F ₁ s ° ] (Wᴰ _ _ _ (f p) °)) ≃ ((Σ[ p ∈ Pos F ₁ s ] Wᴰ _ _ _ (f p)) °)
    Σ-isolate-equiv s f .fst = _
    Σ-isolate-equiv s f .snd = is-equiv-Σ-isolate s f


{- Direct equivalence
  μ-rule-shape≃ : Shape (μ G) ≃ Shape (∂ tt° (μ F))
  μ-rule-shape≃ =
    Shape (μ G)
      ≃⟨⟩
    W (Shape G) (Pos G ₁)
      ≃⟨ W-out-equiv ⟩
    Σ[ t ∈ Shape G ] (Pos G ₁ t → W (Shape G) (Pos G ₁))
      ≃⟨⟩
    Σ[ t ∈ _ ⊎ (_ × 𝟙) ] _
      ≃⟨ Σ-⊎-fst-≃ ⟩
    _ ⊎ Σ (_ × 𝟙) _
      ≃⟨ ⊎-right-≃ (isoToEquiv (Σ-cong-iso-fst rUnit×Iso)) ⟩
    (Σ[ t ∈ Shape (∂ ₀° F [ μ F ]) ] (𝟘* → W (Shape G) (Pos G ₁)))
      ⊎
    (Σ[ x ∈ _ ] (𝟘* ⊎ 𝟙 → W _ _))
    -- (Σ[ x ∈ Σ[ (s , p₁ , _) ∈ Σ[ s ∈ S ] (P ₁ s °) ] ((P ₁ s) ∖ p₁ → W S (P ₁)) ] (𝟘* ⊎ 𝟙 → W _ _))
      ≃⟨ ⊎-equiv (Σ-contractSnd λ _ → Empty.isContrΠ⊥*) (Σ-cong-equiv-snd λ _ → Π-contractDom (isOfHLevelRespectEquiv 0 (⊎-empty-left λ ()) Unit.isContrUnit)) ⟩

    (Shape (∂ ₀° F [ μ F ]))
      ⊎
    (Σ[ x ∈ _ ] W _ _)
      ≃⟨ ⊎-equiv left right ⟩
    -- Σ[ t ∈ (Σ[ (s , _) ∈ Σ[ s ∈ S ] P ₀ s ° ] (P ₁ s → W S (P ₁))) ⊎ ((Σ[ (s , p₁ , _) ∈ Σ[ s ∈ S ] (P ₁ s °) ] ((P ₁ s) ∖ p₁ → W S (P ₁))) × 𝟙) ] (Pos G ₁ t → W (Shape G) (Pos G ₁))
    --   ≃⟨ {! Shape G !} ⟩
    (Σ[ (s , _) ∈ Σ[ s ∈ S ] (P ₁ s → W S (P ₁)) ] P ₀ s °)
      ⊎
    (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P ₁ s → W S (P ₁)) ] Σ[ (p , _) ∈ P ₁ s ° ] (Wᴰ S (P ₁) (P ₀) (f p) °))
      ≃⟨ isoToEquiv $ invIso Σ-⊎-snd-Iso ⟩
    Σ[ (s , f) ∈ Σ[ s ∈ S ] (P ₁ s → W S (P ₁)) ] ((P ₀ s °) ⊎ ((Σ[ (p , _) ∈ P ₁ s ° ] (Wᴰ S (P ₁) (P ₀) (f p) °))))
      ≃⟨ Σ-cong-equiv-snd (uncurry split-isolated) ⟩
    Σ[ (s , f) ∈ Σ[ s ∈ S ] (P ₁ s → W S (P ₁)) ] Wᴰ S (P ₁) (P ₀) (sup s f) °
      ≃⟨ Σ-cong-equiv-fst W-in-equiv ⟩
    Σ[ w ∈ W S (P ₁) ] (Pos (μ F) • w) °
      ≃⟨⟩
    Shape (∂ tt° (μ F))
      ≃∎
    where
      split-isolated : (s : S) (f : P ₁ s → W S (P ₁))
        → ((P ₀ s °) ⊎ ((Σ[ (p , _) ∈ P ₁ s ° ] (Wᴰ S (P ₁) (P ₀) (f p) °))))
            ≃
          Wᴰ S (P ₁) (P ₀) (sup s f) °
      split-isolated s f =
        (P ₀ s °) ⊎ ((Σ[ (p , _) ∈ P ₁ s ° ] (Wᴰ S (P ₁) (P ₀) (f p) °)))
          ≃⟨ ⊎-right-≃ (Σ-isolate _ _ , is-equiv-Σ-isolate s f) ⟩
        (P ₀ s °) ⊎ ((Σ[ p ∈ P ₁ s ] (Wᴰ S (P ₁) (P ₀) (f p))) °)
          ≃⟨ invEquiv IsolatedSumEquiv ⟩
        (P ₀ s ⊎ (Σ[ p ∈ P ₁ s ] (Wᴰ S (P ₁) (P ₀) (f p)))) °
          ≃⟨ IsolatedSubstEquiv (Wᴰ-in-equiv _ _ _ s f) ⟩
        Wᴰ S (P ₁) (P ₀) (sup s f) °
          ≃∎

      left : (Shape (∂ ₀° F [ μ F ])) ≃ (Σ[ (s , _) ∈ Σ[ s ∈ S ] (P ₁ s → W S (P ₁)) ] P ₀ s °)
      left = strictEquiv (λ { ((s , p₀°) , f) → ((s , f) , p₀°) }) (λ { ((s , f) , p₀°) → ((s , p₀°) , f) })

      right : (Σ[ x ∈ Shape (∂ ₁° F [ μ F ]) ] W _ _) ≃ (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P ₁ s → W S (P ₁)) ] Σ[ (p , _) ∈ P ₁ s ° ] (Wᴰ S (P ₁) (P ₀) (f p) °))
      right =
        (Σ[ x ∈ _ ] W _ _)
          ≃⟨ Σ-assoc-≃ ⟩
        Σ[ (s , p , _) ∈ Σ[ s ∈ S ] P ₁ s ° ] ((P ₁ s ∖ p → Shape (μ F)) × W (Shape G) (Pos G ₁))
          ≃⟨ Σ-assoc-≃ ⟩
        Σ[ s ∈ S ] Σ[ (p , _) ∈ P ₁ s ° ] ((P ₁ s ∖ p → Shape (μ F)) × W (Shape G) (Pos G ₁))
          ≃⟨ {! !} ⟩
        (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P ₁ s → W S (P ₁)) ] Σ[ (p , _) ∈ P ₁ s ° ] (Wᴰ S (P ₁) (P ₀) (f p) °))
          ≃∎
-}

  μ-rule-shape-rec : (t : Shape G)
    → (Pos G ₁ t → Shape (∂ tt° (μ F)))
    → Shape ((∂ tt° (μ F)))
  μ-rule-shape-rec (inl ((s , p₀) , f)) rec = sup s f , top° p₀
  μ-rule-shape-rec (inr (((s , p₁) , f) , _)) rec
    using (w , wᴰ) ← rec (inr •)
    = sup s (stitch p₁ (f , w)) , below° (p₁ ,° subst° (Pos (μ F) •) (sym (stitch-β p₁ f {w})) wᴰ)

  μ-rule-shape : Shape (μ G) → Shape ((∂ tt° (μ F)))
  μ-rule-shape = W-elim λ t _ → μ-rule-shape-rec t

  {-
  -- U : Type
  -- U = W (Σ[ s ∈ S ] P ₁ s °) λ (s , p₁) → P ₁ s - p₁

  U' : Type
  U' = (Σ[ s ∈ S ] Σ[ p₀ ∈ P ₀ s ° ] (P ₁ s → W S (P ₁))) ⊎ (Σ[ s ∈ S ] Σ[ p₁ ∈ P ₁ s ° ] (P ₁ s - p₁ → W S (P ₁)))

  R' : U' → Type
  R' (inl (s , p₀ , _)) = 𝟘
  R' (inr (s , (p₁ , _) , f)) = {! Shape (μ G)!}

  μ-rule-shape' : Shape (μ G) → W U' R'
  μ-rule-shape' = W-elim λ where
    (inl ((s , p₀) , f)) _ rec → sup (inl (s , p₀ , f)) λ () -- sup s f , top (p₀ .fst) , isIsolatedTop (p₀ .snd)
    (inr (((s , p₁) , f) , _)) _ rec → sup (inr (s , p₁ , f)) {! W-shape (rec (inr •)) !}
      -- let (w , wᴰ) = rec (inr •)
      -- in sup s (stitch p₁ (f , w))
      --   , below (p₁ .fst) (subst (Pos (μ F) •) (sym (stitch-β p₁ f {w})) (wᴰ .fst))
      --   , isIsolatedBelow (isIsolatedΣ (p₁ .snd) (isIsolatedSubst (Pos (μ F) •) (sym (stitch-β p₁ f {w})) (wᴰ .snd)))
  -}

  -- Explicit W-induction to convince Agda that this a terminating procedure.
  μ-rule-shape⁻¹-rec : (s : S) (f : P ₁ s → W S (P ₁))
    → (rec : (p₁ : P ₁ s) → (Pos (μ F) • (f p₁) °) → Shape (μ G))
    → Pos (μ F) • (sup s f) ° → Shape (μ G)
  μ-rule-shape⁻¹-rec s f _ (top p₀ , isolated-top-p₀) = sup (inl ((s , (p₀ , isIsolatedFromTop isolated-top-p₀)) , f)) λ ()
  μ-rule-shape⁻¹-rec s f rec (below p₁ wᴰ , isolated-below-p₁-wᴰ) =
    sup (inr (((s , p₁ , isolated-p₁) , f ∘ fst) , •)) λ where
      (inr •) → rec p₁ (wᴰ , isolated-wᴰ)
    module μ-rule-shape⁻¹-rec where
      isolated-p₁-wᴰ = isEquiv-Σ-isolate→isIsolatedPair (is-equiv-Σ-isolate s f) (isIsolatedFromBelow isolated-below-p₁-wᴰ)

      isolated-p₁ : isIsolated p₁
      isolated-p₁ = isolated-p₁-wᴰ .fst

      isolated-wᴰ : isIsolated wᴰ
      isolated-wᴰ = isolated-p₁-wᴰ .snd

  μ-rule-fib : (y : Shape ((∂ tt° (μ F)))) → fiber μ-rule-shape y
  μ-rule-fib = uncurry $ W-elim μ-rule-fib-rec where
    module _ (s : S) (f : P ₁ s → W S (P ₁))
      (rec : ∀ p y → fiber μ-rule-shape (f p , y))
      where
      μ-rule-fib-rec : (w : Wᴰ _ _ _ (sup s f) °) → fiber μ-rule-shape (sup s f , w)
      μ-rule-fib-rec (top p₀ , isolated-top-p₀) .fst = sup (inl ((s , (p₀ , isIsolatedFromTop isolated-top-p₀)) , f)) λ ()
      μ-rule-fib-rec (top p₀ , isolated-top-p₀) .snd = curry ΣPathP (refl′ (sup s f)) (Isolated≡ $ refl′ $ top p₀)
      μ-rule-fib-rec (below p₁ wᴰ , isolated-below-p₁-wᴰ) = fib
        where
          isolated-p₁-wᴰ : isIsolated p₁ × isIsolated wᴰ
          isolated-p₁-wᴰ = isEquiv-Σ-isolate→isIsolatedPair (is-equiv-Σ-isolate s f) (isIsolatedFromBelow isolated-below-p₁-wᴰ)

          isolated-p₁ : isIsolated p₁
          isolated-p₁ = isolated-p₁-wᴰ .fst

          p₁° : P ₁ s °
          p₁° = p₁ , isolated-p₁

          isolated-wᴰ : isIsolated wᴰ
          isolated-wᴰ = isolated-p₁-wᴰ .snd

          fib-rec : fiber μ-rule-shape (f p₁ , wᴰ , isolated-wᴰ)
          fib-rec = rec p₁ (wᴰ , isolated-wᴰ)

          fib : fiber μ-rule-shape (sup s f , below p₁ wᴰ , isolated-below-p₁-wᴰ)
          fib .fst = sup (inr (((s , p₁ , isolated-p₁) , f ∘ fst) , •)) λ where
            (inr •) → fib-rec .fst
          fib .snd = ΣPathP (cong (sup s) lemma₁ , IsolatedPathP {B = Pos (μ F) •} {p = cong (sup s) lemma₁} lemma₂)
            where
              μˢ : Shape (μ F)
              μˢ = μ-rule-shape (fib-rec .fst) .fst

              μᵖ : Pos (μ F) • μˢ
              μᵖ = μ-rule-shape (fib-rec .fst) .snd .fst

              μˢ-path : μˢ ≡ f p₁
              μˢ-path = cong fst (fib-rec .snd)

              μᵖ-path : PathP (λ i → Pos (μ F) • (μˢ-path i)) μᵖ wᴰ
              μᵖ-path = cong (fst ∘ snd) (fib-rec .snd)

              μˢ-adjust : μˢ ≡ stitch p₁° (f ∘ fst , μˢ) p₁
              μˢ-adjust = sym $ stitch-β p₁° (f ∘ fst)

              μˢ-adjust-filler : PathP (λ i → Pos (μ F) • (μˢ-adjust i)) μᵖ (subst (Pos (μ F) •) μˢ-adjust μᵖ)
              μˢ-adjust-filler = subst-filler (Pos (μ F) •) μˢ-adjust μᵖ

              -- This uses the second component (a path) of the recursive call:
              opaque
                lemma₁ : stitch p₁° (f ∘ fst , μˢ) ≡ f
                lemma₁ = stitch-eval p₁° f μˢ μˢ-path
 
                ---                  μᵖ-path
                ---           μˢ -------------> f p₁
                ---            ^                 ^
                ---            |                 |
                --- ~μˢ-adjust |                 | =
                ---            |                 |
                ---            |                 |
                ---            ' -------------> f p₁
                ---               lemma₁ ≡$ p₁
                lemma₁-filler : Square (sym μˢ-adjust) (refl′ (f p₁)) (lemma₁ ≡$ p₁) μˢ-path
                lemma₁-filler = stitch-eval-yes-filler p₁° f μˢ μˢ-path

              --- q ≝ μˢ-path
              ---               lemma₁ ≡$ p₁
              ---           . -------------> f p₁
              ---           ^ ↖      =      ↗ ^
              ---           |  .---------->.  |
              --- μˢ-adjust |= | l₁-filler |  | q
              ---           |  '-----q---->'  |
              ---     ⱼ     | ↙          ~q ↘ |
              ---     ↑    μˢ --------------> μˢ
              ---      →ᵢ            =
              sq : Square
                μˢ-adjust
                μˢ-path
                (refl′ μˢ)
                (lemma₁ ≡$ p₁)
              sq i j = hcompᴵ (∂ᴵ i ∨ ∂ᴵ j) λ where
                k (k = i0) → lemma₁-filler i (~ j)
                k (i = i0) → μˢ-adjust j
                k (i = i1) → μˢ-path (~ k ∨ j)
                k (j = i0) → μˢ-path (~ k ∧ i)
                k (j = i1) → lemma₁ i p₁

              lemma₃ : PathP (λ i → Wᴰ S (P ₁) (P ₀) (lemma₁ i p₁)) (subst (Pos (μ F) •) μˢ-adjust μᵖ) wᴰ
              lemma₃ = doubleCompPathP (Wᴰ S (P ₁) (P ₀)) sq (symP μˢ-adjust-filler) (refl′ μᵖ) μᵖ-path

              lemma₂ : PathP (λ i → Wᴰ S (P ₁) (P ₀) (sup s (lemma₁ i)))
                (below p₁ ((subst (Pos (μ F) •) μˢ-adjust μᵖ)))
                (below p₁ wᴰ)
              lemma₂ = Wᴰ-Path→≡ S (P ₁) (P ₀) (refl′ p₁ , lemma₃)

  μ-rule-shape⁻¹ : Shape ((∂ tt° (μ F))) → Shape (μ G)
  μ-rule-shape⁻¹ = fst ∘ μ-rule-fib

  isEmbedding-μ-rule-shape : isEmbedding μ-rule-shape
  isEmbedding-μ-rule-shape = {! isEmbeddingComp !}

  μ-rule-is-prop-fib : ∀ y → isProp (fiber μ-rule-shape y)
  μ-rule-is-prop-fib = uncurry $ W-elim μ-rule-is-prop-fib-rec where module _ (s : S) (f : P ₁ s → W S (P ₁)) where
    FiberL : (y : (Pos (μ F) • (sup s f)) °) → Type _
    FiberL y = fiber top° y

    isPropFiberL : ∀ y → isProp (FiberL y)
    isPropFiberL y = isEmbedding→hasPropFibers isEmbeddingTop° y

    fiber-equiv-left : (y : (Pos (μ F) • (sup s f)) °) →
      (FiberL y)
        ≃
      (Σ[ t@((s′ , p₀) , f′) ∈ Shape (∂ ₀° F [ μ F ]) ] Σ[ _ ∈ (𝟘* → W (Shape G) (Pos G ₁)) ] (sup s′ f′ , top° p₀) ≡ (sup s f , y))
    fiber-equiv-left y =
      fiber top° y
        ≃⟨⟩
      Σ[ p₀ ∈ P ₀ s ° ]
        Path (Wᴰ _ _ (P ₀) (sup s f) °) (top° p₀) y
        ≃⟨ invEquiv $ Σ-contractFst $ isContrRetract {B = singl (sup s f)}
          (λ { (sup s′ f′ , sup-path) → sup s′ f′ , sym sup-path })
          (λ { (sup s′ f′ , sup-path) → sup s′ f′ , sym sup-path })
          (λ { (sup s′ f′ , sup-path) → refl })
          (isContrSingl _)
        ⟩
      Σ[ (w′ , w-path) ∈ Σ[ w′ ∈ W S (P ₁) ] sup (W-shape w′) (W-branch w′) ≡ sup s f ]
        Σ[ p₀ ∈ P ₀ (W-shape w′) ° ]
        PathP (λ i → Pos (μ F) • (w-path i) °) (top° p₀) y
        ≃⟨ strictEquiv (λ { ((w′ , w-path) , p₀ , top≡y) → (w′ , p₀ , w-path , top≡y) }) (λ { (w′ , p₀ , w-path , top≡y) → ((w′ , w-path) , p₀ , top≡y) }) ⟩
      Σ[ w′ ∈ W S (P ₁) ]
        Σ[ p₀ ∈ P ₀ (W-shape w′) ° ]
        Σ[ w-path ∈ sup (W-shape w′) (W-branch w′) ≡ sup s f ]
        PathP (λ i → Pos (μ F) • (w-path i) °) (top° p₀) y
        ≃⟨ Σ-cong-equiv-fst W-out-equiv ⟩
      Σ[ (s′ , f′) ∈ Σ[ s′ ∈ S ] (P ₁ s′ → W S (P ₁)) ]
        Σ[ p₀ ∈ P ₀ s′ ° ]
        Σ[ w-path ∈ sup s′ f′ ≡ sup s f ]
        PathP (λ i → Pos (μ F) • (w-path i) °) (top° p₀) y
        ≃⟨ strictEquiv (λ { ((s′ , f′) , p₀ , w-path , wᴰ-path) → (((s′ , p₀) , f′) , w-path , wᴰ-path) }) (λ { (((s′ , p₀) , f′) , w-path , wᴰ-path) → ((s′ , f′) , p₀ , w-path , wᴰ-path) }) ⟩
      Σ[ t@((s′ , p₀) , f′) ∈ Shape (∂ ₀° F [ μ F ]) ]
      Σ[ w-path ∈ sup s′ f′ ≡ sup s f ]
        PathP (λ i → Pos (μ F) • (w-path i) °) (top° p₀) y
        ≃⟨ Σ-cong-equiv-snd (λ t → ΣPathP≃PathPΣ) ⟩
      Σ[ t@((s′ , p₀) , f′) ∈ Shape (∂ ₀° F [ μ F ]) ]
        (sup s′ f′ , top° p₀) ≡ (sup s f , y)
        ≃⟨ Σ-cong-equiv-snd (λ t → invEquiv $ Σ-contractFst Empty.isContrΠ⊥*) ⟩
      Σ[ t@((s′ , p₀) , f′) ∈ Shape (∂ ₀° F [ μ F ]) ]
      Σ[ _ ∈ (𝟘* → W (Shape G) (Pos G ₁)) ]
        (sup s′ f′ , top° p₀) ≡ (sup s f , y)
        ≃∎

    Σ-below° : (Σ[ p₁ ∈ P ₁ s ° ] Wᴰ _ _ (P ₀) (f (p₁ .fst)) °) → Wᴰ S _ _ (sup s f) °
    Σ-below° = Σ-isolate _ _ ⨟ below°

    is-embedding-Σ-below° : isEmbedding Σ-below°
    is-embedding-Σ-below° = isEmbeddingComp (Σ-isolate _ _) below° (isEquiv→isEmbedding (is-equiv-Σ-isolate s f)) isEmbeddingBelow°

    FiberR : (y : Pos (μ F) • (sup s f) °) → Type _
    FiberR y = Σ[ ((p₁ , wᴰ), _) ∈ fiber Σ-below° y ] fiber μ-rule-shape (f (p₁ .fst) , wᴰ)

    isPropFiberR :
      (_ : ∀ p₁ → (y : Pos (μ F) • (f p₁) °) → isProp (fiber μ-rule-shape (f p₁ , y)))
      → ∀ y → isProp (FiberR y)
    isPropFiberR is-prop-rec y = isPropΣ
      (isEmbedding→hasPropFibers is-embedding-Σ-below° y)
      (λ { ((p₁ , wᴰ) , _) → is-prop-rec (p₁ .fst) wᴰ })

    fiber-equiv-right : (y : Pos (μ F) • (sup s f) °) →
      FiberR y
        ≃
      (Σ[ t ∈ (Shape (↑ (∂ ₁° F [ μ F ]) ⊗ π₁)) ] Σ[ g ∈ (Pos G ₁ (inr t) → W (Shape G) (Pos G ₁)) ] μ-rule-shape-rec (inr t) (μ-rule-shape ∘ g) ≡ (sup s f , y))
    fiber-equiv-right y =
      Σ[ ((p₁ , wᴰ), _) ∈ fiber Σ-below° y ] fiber μ-rule-shape (f (p₁ .fst) , wᴰ)
        ≃⟨ strictEquiv
          (λ { (((p₁ , wᴰ) , below≡y) , fiber-μ-rule) → (p₁ , wᴰ , fiber-μ-rule , below≡y) })
          (λ { (p₁ , wᴰ , fiber-μ-rule , below≡y) → (((p₁ , wᴰ) , below≡y) , fiber-μ-rule) })
        ⟩
      (Σ[ p₁ ∈ P ₁ s ° ]
        Σ[ wᴰ ∈ Pos (μ F) • (f (p₁ .fst)) ° ]
          fiber μ-rule-shape (f (p₁ .fst) , wᴰ)
            ×
          (Path (Pos (μ F) • (sup s f) °) (below° (p₁ ,° wᴰ)) y)
      )
        ≃⟨ invEquiv $ Σ-contractFst $ isContrSingl f ⟩
      (Σ[ (f′ , f-path) ∈ singl f ]
        Σ[ p₁ ∈ P ₁ s ° ]
        Σ[ wᴰ ∈ Pos (μ F) • (f′ (p₁ .fst)) ° ]
          fiber μ-rule-shape (f′ (p₁ .fst) , wᴰ)
            ×
          (PathP (λ i → Pos (μ F) • (sup s (f-path (~ i))) °)
              (below° (p₁ ,° wᴰ))
              y
          )
      )
        ≃⟨ invEquiv $ Σ-contractFst $ isContrSingl s ⟩
      (Σ[ (s′ , s-path) ∈ singl s ]
        Σ[ (f′ , f-path) ∈ singlP (λ i → P ₁ (s-path i) → W S (P ₁)) f ]
        Σ[ p₁ ∈ P ₁ s′ ° ]
        Σ[ wᴰ ∈ Pos (μ F) • (f′ (p₁ .fst)) ° ]
          fiber μ-rule-shape (f′ (p₁ .fst) , wᴰ)
            ×
          (PathP (λ i → Pos (μ F) • (sup (s-path (~ i)) (f-path (~ i))) °)
              (below° (p₁ ,° wᴰ))
              y
          )
      )
        ≃⟨ ?
          -- strictEquiv
          -- (λ { ((s′ , s≡) , (f′ , f≡) , rest) → (s′ , f′ , (sym s≡ , symP f≡) , rest) })
          -- (λ { (s′ , f′ , (s≡ , f≡) , rest) → ((s′ , sym s≡) , (f′ , symP f≡) , rest) })
        ⟩
      {-
      (Σ[ s′ ∈ S ]
        Σ[ s≡ ∈ s′ ≡ s ]
        Σ[ f′ ∈ (P ₁ s′ → W S (P ₁)) ]
        Σ[ f≡ ∈ PathP ? f f′ ]
        Σ[ p₁ ∈ P ₁ s′ ° ]
        Σ[ wᴰ ∈ Pos (μ F) • (f′ (p₁ .fst)) ° ]
          fiber μ-rule-shape (f′ (p₁ .fst) , wᴰ)
            ×
          (PathP (λ i → Pos (μ F) • (sup (s≡ i) (f≡ (~ i))) °)
              (below° (p₁ ,° wᴰ))
              y
          )
      )
        ≃⟨ ? ⟩
      -}
      (Σ[ s′ ∈ S ]
        Σ[ f′ ∈ (P ₁ s′ → W S (P ₁)) ]
        Σ[ w-path ∈ sup s′ f′ ≡ sup s f ]
        Σ[ p₁ ∈ P ₁ s′ ° ]
        Σ[ wᴰ ∈ Pos (μ F) • (f′ (p₁ .fst)) ° ]
          fiber μ-rule-shape (f′ (p₁ .fst) , wᴰ)
            ×
            PathP (λ i → Pos (μ F) • (w-path i) °) (below° (p₁ ,° wᴰ)) y
      )
        ≃⟨
          strictEquiv
          (λ { (s′ , f′ , w-path , p₁ , wᴰ , fib , wᴰ-path) → (s′ , p₁ , f′ , wᴰ , fib , w-path , wᴰ-path) })
          (λ { (s′ , p₁ , f′ , wᴰ , fib , w-path , wᴰ-path) → (s′ , f′ , w-path , p₁ , wᴰ , fib , wᴰ-path) })
        ⟩
      (Σ[ s′ ∈ S ]
        Σ[ p₁ ∈ P ₁ s′ ° ]
        Σ[ f′ ∈ (P ₁ s′ → W S (P ₁)) ]
        Σ[ wᴰ ∈ Pos (μ F) • (f′ (p₁ .fst)) ° ]
          fiber μ-rule-shape (f′ (p₁ .fst) , wᴰ)
            ×
          (Σ[ w-path ∈ sup s′ f′ ≡ sup s f ]
            PathP (λ i → Pos (μ F) • (w-path i) °) (below° (p₁ ,° wᴰ)) y
          )
      )
        ≃⟨ Σ-cong-equiv-snd (λ s′ → Σ-cong-equiv-snd λ p₁ → Σ-cong-equiv (unstitchEquiv p₁) λ f′ → Σ-cong-equiv-snd λ wᴰ → Σ-cong-equiv-snd λ _ → Σ-cong-equiv (compPathlEquiv $ cong (sup s′) $ retEq (unstitchEquiv p₁) f′) {! !}) ⟩
      (Σ[ s′ ∈ S ]
        Σ[ p₁ ∈ P ₁ s′ ° ]
        Σ[ (f′ , w) ∈ (P ₁ s′ - p₁ → W S (P ₁)) × W S (P ₁) ]
        Σ[ wᴰ ∈ Pos (μ F) • w ° ]
          fiber μ-rule-shape (w , wᴰ)
            ×
          (Σ[ w-path ∈ sup s′ (stitch p₁ (f′ , w)) ≡ sup s f ]
            PathP (λ i → Pos (μ F) • (w-path i) °)
              (below° (p₁ ,° subst° (Pos (μ F) •) (sym (stitch-β p₁ f′)) wᴰ))
              y
          )
      )
        ≃⟨ {! !} ⟩
      (Σ[ t@(((s′ , p₁) , f′) , •) ∈ (Shape (↑ (∂ ₁° F [ μ F ]) ⊗ π₁)) ]
        Σ[ w-wᴰ ∈ Shape (∂ tt° (μ F)) ]
          fiber μ-rule-shape w-wᴰ
            ×
          (Σ[ w-path ∈ sup s′ (stitch p₁ (f′ , w-wᴰ .fst)) ≡ sup s f ]
            PathP (λ i → Pos (μ F) • (w-path i) °)
              (below° (p₁ ,° subst° (Pos (μ F) •) (sym (stitch-β p₁ f′)) (w-wᴰ .snd)))
              y
          )
      )
        ≃⟨ {! !} ⟩
      (Σ[ t@(((s′ , p₁) , f′) , _) ∈ (Shape (↑ (∂ ₁° F [ μ F ]) ⊗ π₁)) ]
        Σ[ w-wᴰ ∈ Shape (∂ tt° (μ F)) ]
          fiber μ-rule-shape w-wᴰ
            ×
          Path (Σ[ w ∈ W S (P ₁) ] Pos (μ F) • w °)
            (sup s′ (stitch p₁ (f′ , w-wᴰ .fst)) , below° (p₁ ,° subst° (Pos (μ F) •) (sym (stitch-β p₁ f′)) (w-wᴰ .snd)) )
            (sup s f , y)
      )
        ≃⟨ {! !} ⟩
      (Σ[ t@(((s′ , p₁) , f′) , _) ∈ (Shape (↑ (∂ ₁° F [ μ F ]) ⊗ π₁)) ]
        Σ[ w-wᴰ ∈ Shape (∂ tt° (μ F)) ]
        fiber μ-rule-shape w-wᴰ
          ×
        Path (Σ[ w ∈ W S (P ₁) ] Pos (μ F) • w °)
          (sup s′ (stitch p₁ (f′ , w-wᴰ .fst)) , below° (p₁ ,° subst° (Pos (μ F) •) (sym (stitch-β p₁ f′)) (w-wᴰ .snd)) )
          (sup s f , y)
      )
        ≃⟨ Σ-cong-equiv-snd (λ t → strictEquiv (λ { ((w , wᴰ) , (x , y) , Σ-path) → {! !} }) {! !}) ⟩
      (Σ[ t@(((s′ , p₁) , f′) , _) ∈ (Shape (↑ (∂ ₁° F [ μ F ]) ⊗ π₁)) ]
        Σ[ g ∈ (W (Shape G) (Pos G ₁)) ]
        Σ[ (w-wᴰ , _) ∈ Σ[ w-wᴰ ∈ _ ] (μ-rule-shape g) ≡ w-wᴰ ]
        Path (Σ[ w ∈ W S (P ₁) ] Pos (μ F) • w °)
          (sup s′ (stitch p₁ (f′ , w-wᴰ .fst)) , below° (p₁ ,° subst° (Pos (μ F) •) (sym (stitch-β p₁ f′)) (w-wᴰ .snd)) )
          (sup s f , y)
      )
        ≃⟨ Σ-cong-equiv-snd (λ { t@(((s′ , p₁) , f′) , _) → Σ-cong-equiv-snd λ g → Σ-contractFst $ isContrSingl $ μ-rule-shape g }) ⟩
      (Σ[ t@(((s′ , p₁) , f′) , _) ∈ (Shape (↑ (∂ ₁° F [ μ F ]) ⊗ π₁)) ]
        Σ[ g ∈ (W (Shape G) (Pos G ₁)) ]
        let w-wᴰ = μ-rule-shape g in
        (sup s′ (stitch p₁ (f′ , w-wᴰ .fst)) , below° (p₁ ,° subst° (Pos (μ F) •) (sym (stitch-β p₁ f′)) (w-wᴰ .snd)) ) ≡ (sup s f , y)
      )
        ≃⟨⟩
      (Σ[ t ∈ (Shape (↑ (∂ ₁° F [ μ F ]) ⊗ π₁)) ]
        Σ[ g ∈ (W (Shape G) (Pos G ₁)) ]
        μ-rule-shape-rec (inr t) (μ-rule-shape ∘ const g) ≡ (sup s f , y)
      )
        ≃⟨ Σ-cong-equiv-snd (λ t → Σ-cong-equiv-fst $ invEquiv $ contractDomainEquiv $ is-contr-𝟘⊎𝟙) ⟩
      (Σ[ t ∈ (Shape (↑ (∂ ₁° F [ μ F ]) ⊗ π₁)) ]
        Σ[ g ∈ (Lift 𝟘 ⊎ 𝟙 → W (Shape G) (Pos G ₁)) ]
        μ-rule-shape-rec (inr t) (μ-rule-shape ∘ g) ≡ (sup s f , y)
      )
        ≃∎
        where
          is-contr-𝟘⊎𝟙 : isContr (Lift 𝟘 ⊎ 𝟙)
          is-contr-𝟘⊎𝟙 = isOfHLevelRespectEquiv 0 (⊎-empty-left λ ()) Unit.isContrUnit

    Fiber : (y : Pos (μ F) • (sup s f) °) → Type _
    Fiber y = FiberL y ⊎ FiberR y

    fiber-equiv : ∀ y → (Fiber y) ≃ (fiber μ-rule-shape (sup s f , y))
    fiber-equiv y =
      (fiber top° y) ⊎ {! !}
        ≃⟨ ⊎-equiv (fiber-equiv-left y) (fiber-equiv-right y) ⟩
      (
        (Σ[ t@((s′ , p₀) , f′) ∈ Shape (∂ ₀° F [ μ F ]) ]
          Σ[ _ ∈ (Pos G ₁ (inl t) → W (Shape G) (Pos G ₁)) ]
          (sup s′ f′ , top° p₀) ≡ (sup s f , y))
          ⊎
        (Σ[ t ∈ (Shape (↑ (∂ ₁° F [ μ F ]) ⊗ π₁)) ]
          Σ[ g ∈ (Pos G ₁ (inr t) → W (Shape G) (Pos G ₁)) ]
          μ-rule-shape-rec (inr t) (μ-rule-shape ∘ g) ≡ (sup s f , y)
        )
      )
        ≃⟨ invEquiv Σ-⊎-fst-≃ ⟩
      Σ[ t ∈ Shape G ] Σ[ g ∈ (Pos G ₁ t → W (Shape G) (Pos G ₁)) ] μ-rule-shape-rec t (μ-rule-shape ∘ g) ≡ (sup s f , y)
        ≃⟨ invEquiv Σ-assoc-≃ ⟩
      Σ[ x ∈ Σ[ t ∈ Shape G ] (Pos G ₁ t → W (Shape G) (Pos G ₁)) ] μ-rule-shape-rec (x .fst) (μ-rule-shape ∘ x .snd) ≡ (sup s f , y)
        ≃⟨ Σ-cong-equiv-fst W-in-equiv ⟩
      Σ[ x ∈ Shape (μ G) ] μ-rule-shape x ≡ (sup s f , y)
        ≃∎

    μ-rule-is-prop-fib-rec : (∀ p₁ → (y : Pos (μ F) • (f p₁) °) → isProp (fiber μ-rule-shape (f p₁ , y)))
      → ∀ y → isProp (fiber μ-rule-shape (sup s f , y))
    μ-rule-is-prop-fib-rec rec y = isOfHLevelRespectEquiv 1 (fiber-equiv y) isPropFiber where
      excl : FiberL y → FiberR y → 𝟘
      excl = {! !}

      isPropFiber : isProp (Fiber y)
      isPropFiber = isProp⊎ (isEmbedding→hasPropFibers isEmbeddingTop° y) (isPropFiberR rec y) excl


  μ-rule-shape-linv : retract μ-rule-shape μ-rule-shape⁻¹
  μ-rule-shape-linv (sup (inl ((s , p₀ , _) , f)) g) = cong₂ sup shape-path branch-path where
    shape-path : inl ((s , p₀ , _) , f) ≡ inl ((s , p₀ , _) , f)
    shape-path = cong inl $ ΣPathP λ where
      .fst → ΣPathP λ where
        .fst → refl′ s
        .snd → Isolated≡ $ refl′ p₀
      .snd → refl′ f

    branch-path : PathP (λ i → Pos G ₁ (shape-path i) → W _ _) (λ ()) g
    branch-path = funExt λ ()
  μ-rule-shape-linv (sup (inr (((s , p₁°@(p₁ , _)) , f) , •)) g) = cong₂ sup shape-path {! !} where
    ∂f : P ₁ s → Shape (μ F)
    ∂f = stitch p₁° (f , μ-rule-shape (g (inr •)) .fst)

    f′ : Pos (∂ ₁° F) ₁ (s , p₁°) → Shape (μ F)
    f′ = ∂f ∘ fst

    isolated-path : (s , p₁ , _) ≡ (s , p₁°)
    isolated-path = ΣPathP λ where
      .fst → refl′ s
      .snd → Isolated≡ $ refl′ p₁

    -- foo : PathP (λ i → 

    shape-path : inr (((s , p₁ , _) , f′) , •) ≡ inr (((s , p₁ , _) , f) , •)
    shape-path = cong inr $ ΣPathP λ where
      .fst → ΣPathP λ where
        .fst → isolated-path
        .snd → {! μ-rule-shape (g (inr •)) .fst!}
      .snd → refl
    -- (cong inr $ ΣPathP (ΣPathP (ΣPathP (refl′ s , Isolated≡ refl) , {! !}) , refl)) {! !}

  μ-rule-shape-Iso : Iso (Shape (μ G)) (Shape ((∂ tt° (μ F))))
  μ-rule-shape-Iso .Iso.fun = μ-rule-shape
  μ-rule-shape-Iso .Iso.inv = μ-rule-shape⁻¹
  μ-rule-shape-Iso .Iso.rightInv = snd ∘ μ-rule-fib
  μ-rule-shape-Iso .Iso.leftInv = μ-rule-shape-linv

  -- μ-rule-shape⁻¹ = uncurry $ W-elim λ where
  --   s f rec (top p₀ , isolated-top-p₀) → sup (inl ((s , (p₀ , isIsolatedFromTop isolated-top-p₀)) , f)) λ ()
  --   s f rec (below p₁ wᴰ , isolated-below-p₁-wᴰ) →
  --     let (isolated-p₁ , isolated-wᴰ) = isEquiv-Σ-isolate→isIsolatedPair (is-equiv-Σ-isolate s f) (isIsolatedFromBelow isolated-below-p₁-wᴰ)
  --     in sup (inr (((s , p₁ , isolated-p₁) , f ∘ fst) , •)) λ where
  --       (inr •) → rec p₁ (wᴰ , isolated-wᴰ)

  -- μ-rule-shape' : Shape ((∂ tt° (μ F))) → Shape (μ G)
  -- μ-rule-shape' (sup s f , (top p₀ , isolated-top-p₀)) = sup (inl ((s , (p₀ , isIsolatedFromTop isolated-top-p₀)) , f)) λ ()
  -- μ-rule-shape' (sup s f , (below p₁ wᴰ , isolated-below-p₁-wᴰ)) =
  --   let (isolated-p₁ , isolated-wᴰ) = isEquiv-Σ-isolate→isIsolatedPair (is-equiv-Σ-isolate s f) (isIsolatedFromBelow isolated-below-p₁-wᴰ)
  --   in sup (inr (((s , p₁ , isolated-p₁) , f ∘ fst) , •)) λ where
  --     (inr •) → curry μ-rule-shape' (f p₁) (wᴰ , isolated-wᴰ)

{- μ-rule has a righ-inverse
  μ-rule-shape-rinv : section μ-rule-shape μ-rule-shape⁻¹
  μ-rule-shape-rinv = uncurry $ W-elim ind
    where
      ind : (s : S) (f : P ₁ s → W S (P ₁))
        → ((p : P ₁ s) → (pμ : Pos (μ F) • (f p) °) → μ-rule-shape (μ-rule-shape⁻¹ (f p , pμ)) ≡ (f p , pμ))
        → (pμ : Pos (μ F) • (sup s f) °) → μ-rule-shape (μ-rule-shape⁻¹ (sup s f , pμ)) ≡ (sup s f , pμ)
      ind s f section-rec (top p₀ , _) = ΣPathP (refl′ (sup s f) , Isolated≡ (refl′ (top p₀)))
      ind s f section-rec (below p₁ wᴰ , isolated-below-p₁-wᴰ) = goal -- ΣPathP (cong (sup s) goal₁ , {! IsolatedPathP !})
        where
          frob : Shape ((∂ tt° (μ F)))
          frob = μ-rule-shape (μ-rule-shape⁻¹ (sup s f , below p₁ wᴰ , isolated-below-p₁-wᴰ))

          isolated-p₁-wᴰ = isEquiv-Σ-isolate→isIsolatedPair (is-equiv-Σ-isolate s f) (isIsolatedFromBelow isolated-below-p₁-wᴰ)

          isolated-p₁ : isIsolated p₁
          isolated-p₁ = isolated-p₁-wᴰ .fst

          isolated-wᴰ : isIsolated wᴰ
          isolated-wᴰ = isolated-p₁-wᴰ .snd


          p₁° : P ₁ s °
          p₁° = p₁ , isolated-p₁

          goal : μ-rule-shape (μ-rule-shape⁻¹ (sup s f , below p₁ wᴰ , isolated-below-p₁-wᴰ)) ≡ (sup s f , below p₁ wᴰ , isolated-below-p₁-wᴰ)
          goal = curry ΣPathP (WPath→≡ _ _ (refl′ s , funExt {! florp !})) {! !}
            where
              foo : (p : P ₁ s) → μ-rule-shape⁻¹ (f p , {! wᴰ !} , {! !}) ≡ {! !}
              foo = {! !}
              florp : (p : P ₁ s) → stitch p₁° (f ∘ fst , {! !}) p ≡ f p
              florp p = {! stitch-β' p₁° (f ∘ fst) {b₀ =  !}
            {-
            μ-rule-shape (μ-rule-shape⁻¹ (sup s f , below p₁ wᴰ , isolated-below-p₁-wᴰ))
              ≡⟨⟩
            μ-rule-shape (sup (inr (((s , p₁ , isolated-p₁) , f ∘ fst) , •)) _)
              -- ≡⟨ cong (λ - → μ-rule-shape (sup (inr (((s , p₁ , isolated-p₁) , f ∘ fst) , •)) -)) $ funExt (λ { (inr •) → refl′ (μ-rule-shape⁻¹ (f p₁ , (wᴰ , isolated-wᴰ)))}) ⟩
              -- ≡[ i ]⟨ μ-rule-shape (sup (inr (((s , p₁ , isolated-p₁) , f ∘ fst) , •)) λ { (inr •) → {! !} }) ⟩
              ≡⟨ ? ⟩
            μ-rule-shape (sup (inr (((s , p₁ , isolated-p₁) , f ∘ fst) , •)) (λ { (inr •) → μ-rule-shape⁻¹ (f p₁ , (wᴰ , isolated-wᴰ)) }))
              ≡⟨ ? ⟩
            (sup s f , below p₁ wᴰ , isolated-below-p₁-wᴰ)
              ∎
            -}
          -- goal₁ : stitch p₁° (f ∘ fst , frob .fst) ≡ f
          -- goal₁ = {! !}

  {-
  -- μ-rule-shape-rinv (sup s f , top p₀ , _) = ΣPathP (refl , Isolated≡ refl)
  -- μ-rule-shape-rinv (sup s f , below p₁ wᴰ , isolated-below-p₁-wᴰ) = ΣPathP (cong (sup s) {! !} , IsolatedPathP {! !})
  --   where
  --     open μ-rule-shape⁻¹-rec s f (\G
  --     p₁° : P ₁ s °
  --     p₁° = p₁ , isolated-p₁

  --     -- goal₁ : stitch p₁° (f ∘ fst , ?) ? ≡ ?
-}

  μ-rule-shape-linv : retract μ-rule-shape μ-rule-shape⁻¹
  μ-rule-shape-linv (sup (inl ((s , p₀ , _) , f)) g) = cong₂ sup (cong inl (ΣPathP (cong (s ,_) (Isolated≡ (refl′ p₀)) , refl′ f))) $ funExt λ ()
  μ-rule-shape-linv (sup (inr (((s , p₁) , f) , _)) g) = cong₂ sup (cong inr {! !}) {! !}

  -}

{- Prove that μ-rule has contractible fibers, directly
  μ-rule'' : isEquiv μ-rule-shape
  μ-rule'' .equiv-proof = uncurry (W-elim contr-fib) where
    massage-shape : Shape (μ G) ≃ _
    massage-shape =
      Shape (μ G)
        ≃⟨ W-out-equiv ⟩
      Σ (Shape G) (λ t → Pos G ₁ t → W (Shape G) (Pos G ₁))
        ≃⟨ Σ-⊎-fst-≃ ⟩
      (Σ (Shape (∂ ₀° F [ μ F ])) (λ s → Pos G ₁ (inl s) → W (Shape G) (Pos G ₁))
        ⊎
      (Σ (Shape (↑ (∂ ₁° F [ μ F ]) ⊗ π₁)) (λ s → Pos G ₁ (inr s) → W (Shape G) (Pos G ₁))))
        ≃⟨⟩
      ((Shape (∂ ₀° F [ μ F ]) × (𝟘* → W (Shape G) (Pos G ₁)))
        ⊎
      ((Shape (↑ (∂ ₁° F [ μ F ])) × 𝟙) × (𝟘* ⊎ 𝟙 → W (Shape G) (Pos G ₁))))
        ≃⟨ ⊎-equiv
          (Σ-contractSnd λ _ → Empty.isContrΠ⊥*)
          -- (Σ-cong-equiv (isoToEquiv (invIso rUnit×Iso)) λ t → Σ-cong-equiv-fst $ invEquiv (Π-contractDom (isOfHLevelRespectEquiv 0 (⊎-empty-left λ ()) (Unit.isContrUnit))))
          (Σ-cong-equiv (isoToEquiv rUnit×Iso) λ _ → (Π-contractDom (isOfHLevelRespectEquiv 0 (⊎-empty-left λ ()) Unit.isContrUnit)))
        ⟩
      (Shape (∂ ₀° F [ μ F ]))
        ⊎
      (Shape (↑ (∂ ₁° F [ μ F ])) × W (Shape G) (Pos G ₁))
        ≃⟨ ⊎-right-≃ shuffle-right ⟩
      (Shape (∂ ₀° F [ μ F ]))
        ⊎
      {! !}
        ≃∎
        where
          shuffle-right : (Shape (↑ (∂ ₁° F [ μ F ])) × W (Shape G) (Pos G ₁)) ≃ {! !}
          shuffle-right =
            (Shape (↑ (∂ ₁° F [ μ F ])) × (Shape (μ G)))
              ≃⟨ Σ-assoc-≃ ⟩
            Σ (Shape (∂ ₁° F)) _
              ≃⟨ Σ-assoc-≃ ⟩
            Σ[ s ∈ S ] Σ[ p ∈ (P ₁ s) ° ] (P ₁ s - p → Shape (μ F)) × (Shape (μ G))
              ≃⟨ {! !} ⟩
            Σ[ s ∈ S ] Σ[ p ∈ (P ₁ s) ° ] (P ₁ s - p → Shape (μ F)) × (Σ[ y ∈ Shape (∂ tt° (μ F)) ] fiber μ-rule-shape y)
              ≃⟨ {! !} ⟩
            Σ[ s ∈ S ] Σ[ p ∈ (P ₁ s) ° ] Σ[ (f , μs) ∈ ((P ₁ s - p → Shape (μ F)) × Shape (μ F)) ] (Σ[ y ∈ Pos (μ F) • μs ° ] fiber μ-rule-shape (μs , y))
              ≃⟨ Σ-cong-equiv-snd (λ s → Σ-cong-equiv-snd λ p → invEquiv $ Σ-cong-equiv-fst (unstitchEquiv p)) ⟩
            Σ[ s ∈ S ] Σ[ (p , _) ∈ (P ₁ s) ° ] Σ[ f ∈ (P ₁ s → Shape (μ F)) ] (Σ[ y ∈ Pos (μ F) • (f p) ° ] fiber μ-rule-shape (f p , y))
              ≃⟨ {! !} ⟩
            {! !}
              ≃∎


    {-
    massage-fiber : ∀ y → fiber μ-rule-shape y ≃ ?
    massage-fiber y =
      fiber μ-rule-shape y
        ≃⟨ invEquiv $ Σ-cong-equiv-fst (invEquiv massage-shape) ⟩
      fiber (μ-rule-shape ∘ invEq massage-shape) y
        ≃⟨ ⊎-fiber-≃ y ⟩
      (fiber (λ { ((s , p₀ , isolated-p₀) , f) → sup s f , top p₀ , isIsolatedTop isolated-p₀ }) y)
        ⊎
      ?
      -- (fiber (λ { (((s , p₁) , f∣ₚ₁) , w) → sup s (stitch p₁ (f∣ₚ₁ , _)) , {! !} }) y)
        ≃⟨ {! !} ⟩
      {! !}
        ≃∎
    -}

      {-
      (Σ[ ((s , (p₀ , isolated-p₀)) , f) ∈ _ ] (sup s f , top p₀ , isIsolatedTop isolated-p₀) ≡ y )
        ⊎
      (Σ[ t ∈ _ ] Σ[ w ∈ (W (Shape G) (Pos G ₁)) ] (sup (t .fst .fst) (stitch (t .fst .snd) {! !}) , below (t .fst .snd .fst) {! !} , {! !}) ≡ y )
        ≃⟨ ⊎-equiv
          (Σ-cong-equiv-snd λ t → invEquiv (Σ-contractFst Empty.isContrΠ⊥*))
          (Σ-cong-equiv (isoToEquiv (invIso rUnit×Iso)) λ t → Σ-cong-equiv-fst $ invEquiv (Π-contractDom (isOfHLevelRespectEquiv 0 (⊎-empty-left λ ()) (Unit.isContrUnit))))
        ⟩
      (Σ[ t ∈ _ ] Σ[ g ∈ (𝟘* → W _ _) ] μ-rule-shape (sup (inl t) g) ≡ y )
        ⊎
      (Σ[ (t , •) ∈ _ ] Σ[ g ∈ (𝟘* ⊎ 𝟙 → W _ _) ] μ-rule-shape (sup (inr (t , •)) g) ≡ y )
        ≃⟨⟩
      (Σ[ t ∈ _ ] Σ[ g ∈ (Pos G ₁ (inl t) → W _ _) ] μ-rule-shape (sup (inl t) g) ≡ y )
        ⊎
      (Σ[ t ∈ _ ] Σ[ g ∈ (Pos G ₁ (inr t) → W _ _) ] μ-rule-shape (sup (inr t) g) ≡ y )
        ≃⟨ invEquiv Σ-⊎-fst-≃ ⟩
      Σ[ t ∈ Shape G ] Σ[ g ∈ (Pos G ₁ t → W _ _) ] μ-rule-shape (sup t g) ≡ y
        ≃⟨ invEquiv Σ-assoc-≃ ∙ₑ Σ-cong-equiv-fst W-in-equiv ⟩
      Σ[ x ∈ Shape (μ G) ] μ-rule-shape x ≡ y
      -}

    contr-fib : (s : S) (f : P ₁ s → W S (P ₁))
      → ((p₁ : P ₁ s) → (μp : Pos (μ F) • (f p₁) °) → isContr (fiber μ-rule-shape (f p₁ , μp)))
      → ∀ μp → isContr (fiber μ-rule-shape (sup s f , μp))
    contr-fib s f rec (top p₀ , isolated-top-p₀) = {! !} where
      y = (sup s f , top p₀ , isolated-top-p₀)

      fiber-equiv : {! !} ≃ fiber μ-rule-shape y
      fiber-equiv =
        {! !}
          ≃⟨ {! !} ⟩
        (Σ[ t ∈ _ ] Σ[ g ∈ (𝟘* → W _ _) ] {! μ-rule-shape (sup (inl t) g) !} ≡ y )
          ⊎
        (Σ[ (t , •) ∈ _ ] Σ[ g ∈ (𝟘* ⊎ 𝟙 → W _ _) ] μ-rule-shape (sup (inr (t , •)) g) ≡ y )
          ≃⟨⟩
        (Σ[ t ∈ _ ] Σ[ g ∈ (Pos G ₁ (inl t) → W _ _) ] μ-rule-shape (sup (inl t) g) ≡ y )
          ⊎
        (Σ[ t ∈ _ ] Σ[ g ∈ (Pos G ₁ (inr t) → W _ _) ] μ-rule-shape (sup (inr t) g) ≡ y )
          ≃⟨ invEquiv Σ-⊎-fst-≃ ⟩
        Σ[ t ∈ Shape G ] Σ[ g ∈ (Pos G ₁ t → W _ _) ] μ-rule-shape (sup t g) ≡ y
          ≃⟨ invEquiv Σ-assoc-≃ ∙ₑ Σ-cong-equiv-fst W-in-equiv ⟩
        Σ[ x ∈ Shape (μ G) ] μ-rule-shape x ≡ y
          ≃⟨⟩
        fiber μ-rule-shape (sup s f , top p₀ , isolated-top-p₀)
          ≃∎

    contr-fib s f rec (below p₁ wᴰ , isolated-below-p₁-wᴰ) = {! !}
-}

  {-
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
  -}

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

  Σ-isolate-equiv : ∀ (s : S) (f : P ₁ s → W S (P ₁)) → (Σ[ (p , _) ∈ Pos F ₁ s ° ] (μP (f p) °)) ≃ ((Σ[ p ∈ Pos F ₁ s ] μP (f p)) °)
  Σ-isolate-equiv s f .fst = _
  Σ-isolate-equiv s f .snd = isEquiv-Σ-isolate s f

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
      ≃⟨ ⊎-right-≃ $ invEquiv $ Σ-isolate-equiv s f ⟩
    (Pos F ₀ s °) ⊎ (Σ[ (p , _) ∈ Pos F ₁ s ° ] (μP (f p) °))
      ≃∎

  discrete-μP : ∀ w → Discrete (Wᴰ S (P ₁) (P ₀) w)
  discrete-μP (sup s f) (top p₀) = {! isIsolatedFromTop !}
  discrete-μP (sup s f) (below p₁ wᴰ) = {! !}

  discrete-P₁ : ∀ s → Discrete (P ₁ s)
  discrete-P₁ s = {! !}
