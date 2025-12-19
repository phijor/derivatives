{-# OPTIONS -WnoUnsupportedIndexedMatch --lossy-unification --allow-unsolved-metas #-}
module Derivative.Indexed.MuRule where

open import Derivative.Indexed.Container
open import Derivative.Indexed.Mu
open import Derivative.Indexed.Derivative
open import Derivative.Indexed.ChainRule

open import Derivative.Prelude
open import Derivative.Basics.Decidable
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

  _ : (G [ ∂ tt° (μ F) ]) ⊸ ∂ tt° (μ F)
  _ =
    (G [ ∂ tt° (μ F) ])
      ⧟⟨ η₀ ⟩
    ((∂ ₀° F [ μ F ]) ⊕ ((∂ ₁° F [ μ F ]) ⊗ ∂ tt° (μ F)))
      ⊸⟨ binary-chain-rule F (μ F) ⟩
    ∂ tt° (F [ μ F ])
      ⧟⟨ η₁ ⟩
    ∂ tt° (μ F)
      ⊸∎

  α : (G [ ∂ tt° (μ F) ]) ⊸ ∂ tt° (μ F)
  α = (Equiv.as-⊸ η₀) ⋆ binary-chain-rule F (μ F) ⋆ (Equiv.as-⊸ η₁)

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

    is-isolated-pair : ∀ (s : S) (f : P ₁ s → W S (P ₁))
      → {p₁ : P ₁ s} {wᴰ : Wᴰ S (P ₁) (P ₀) (f p₁)}
      → isIsolated (p₁ , wᴰ)
      → isIsolated p₁ × isIsolated wᴰ
    is-isolated-pair s f = isEquiv-Σ-isolate→isIsolatedPair (is-equiv-Σ-isolate s f)

  μ-rule-shape : Shape (μ G) → Shape ((∂ tt° (μ F)))
  μ-rule-shape = μ-rule F ._⊸_.shape

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
          isolated-p₁-wᴰ = is-isolated-pair s f (isIsolatedFromBelow isolated-below-p₁-wᴰ)

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

  isEquiv-α : isContainerEquiv α
  isEquiv-α = goal where
    open Equiv using (shape)

    step : isContainerEquiv (Equiv.as-⊸ η₀ ⋆ binary-chain-rule F (μ F))
    step = isContainerEquivComp (Equiv.as-⊸ η₀) (binary-chain-rule F (μ F)) (equivIsContainerEquiv η₀) is-equiv-chain-rule

    goal : isContainerEquiv (Equiv.as-⊸ η₀ ⋆ binary-chain-rule F (μ F) ⋆ (Equiv.as-⊸ η₁))
    goal = isContainerEquivComp (Equiv.as-⊸ η₀ ⋆ binary-chain-rule F (μ F)) (Equiv.as-⊸ η₁) step (equivIsContainerEquiv η₁)

  isEmbedding-α : isContainerEmbedding α
  isEmbedding-α = isContainerEquiv→isContainerEmbedding {e = α} isEquiv-α

  isEmbedding-μ-rule-shape : isContainerEmbedding (μ-rule F)
  isEmbedding-μ-rule-shape = isEmbedding-μ-rec G (∂ tt° (μ F)) α isEmbedding-α

  μ-rule-is-prop-fib : ∀ y → isProp (fiber μ-rule-shape y)
  μ-rule-is-prop-fib = isEmbedding→hasPropFibers isEmbedding-μ-rule-shape

  isEquiv-μ-rule : isContainerEquiv (μ-rule F)
  isEquiv-μ-rule .equiv-proof y = inhProp→isContr (μ-rule-fib y) (μ-rule-is-prop-fib y)

module isEquiv-μ-rule (F : Container _ 𝟚) (is-equiv-μ-rule : isContainerEquiv (μ-rule F)) where
  open Container F renaming (Shape to S ; Pos to P)
  open μ-rule F using (α ; G ; η₀ ; η₁)

  private
    μP = Wᴰ (Shape F) (Pos F ₁) (Pos F ₀)


    is-equiv-α : isContainerEquiv α
    is-equiv-α = isEquivFrom-μ-rec G (∂ tt° (μ F)) α is-equiv-μ-rule

  isEquiv-chain-rule : isContainerEquiv (binary-chain-rule F (μ F))
  isEquiv-chain-rule = isContainerEquivCompLeftRight η₀ η₁ (binary-chain-rule F (μ F)) is-equiv-α
  
  isEquiv-Σ-isolate : ∀ (s : S) (f : P ₁ s → W S (P ₁)) → isEquiv (Σ-isolate (P ₁ s) (μP ∘ f))
  isEquiv-Σ-isolate = isEquivBinaryChainRule→isEquiv-Σ-isolate F (μ F) isEquiv-chain-rule

  Σ-isolate-equiv : ∀ (s : S) (f : P ₁ s → W S (P ₁)) → (Σ[ (p , _) ∈ Pos F ₁ s ° ] (μP (f p) °)) ≃ ((Σ[ p ∈ Pos F ₁ s ] μP (f p)) °)
  Σ-isolate-equiv s f .fst = _
  Σ-isolate-equiv s f .snd = isEquiv-Σ-isolate s f

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
