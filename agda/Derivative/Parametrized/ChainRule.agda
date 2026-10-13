{-# OPTIONS --safe #-}
module Derivative.Parametrized.ChainRule where

open import Derivative.Prelude
open import Derivative.Basics.Decidable
open import Derivative.Basics.Embedding
open import Derivative.Basics.Sigma
open import Derivative.Basics.Sum

open import Derivative.Isolated
open import Derivative.Remove

open import Derivative.Parametrized.Container
open import Derivative.Parametrized.Derivative

open import Cubical.Foundations.Transport using (substEquiv ; substEquiv' ; subst⁻)
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level
    Ix : Type

open Container

binary-chain-rule :
  ∀ (F : Container ℓ 𝟚)
  → (G : Container ℓ 𝟙)
  → ((∂ ₀° F [ G ]) ⊕ ((∂ ₁° F [ G ]) ⊗ ∂ •° G)) ⊸ ∂ •° (F [ G ])
binary-chain-rule F G =
    L   ⧟⟨ e₁ ⟩
    H₁  ⊸⟨ η ⟩
    H₂  ⧟⟨ e₂ ⟩
    R   ⊸∎
  module binary-chain-rule where
  open Container F renaming (Shape to S ; Pos to P) public
  open Container G renaming (Shape to T ; Pos to Qᵢ) public

  Q = Qᵢ •

  L : Container _ _
  L = (∂ ₀° F [ G ]) ⊕ ((∂ ₁° F [ G ]) ⊗ ∂ •° G)

  R : Container _ _
  R = ∂ •° (F [ G ])

  U₁ : Type _
  U₁ = (Σ[ s ∈ S ] Σ[ f ∈ (P ₁ s → T) ] ((P ₀ s °) ⊎ (Σ[ (p , _) ∈ P ₁ s ° ] (Q (f p) °))))

  f₁ :
    ((Σ[ (s , _) ∈ Σ[ s ∈ S ] P ₀ s ° ] (P ₁ s → T)) ⊎ ((Σ[ (s , p , _) ∈ Σ[ s ∈ S ] P ₁ s ° ] (P ₁ s ∖ p → T)) × (Σ[ t ∈ T ] Q t °)))
      ≃
    U₁
  f₁ =
    ((Σ[ (s , _) ∈ Σ[ s ∈ S ] P ₀ s ° ] (P ₁ s → T)) ⊎ ((Σ[ (s , p , _) ∈ Σ[ s ∈ S ] P ₁ s ° ] (P ₁ s ∖ p → T)) × (Σ[ t ∈ T ] Q t °)))
      ≃⟨ ⊎-equiv Σ-assoc-≃ shuffle-right ⟩
    ((Σ[ s ∈ S ] P ₀ s ° × (P ₁ s → T)) ⊎ (Σ[ s ∈ S ] Σ[ (p , _) ∈ P ₁ s ° ] Σ[ (_ , t) ∈ (P ₁ s ∖ p → T) × T ] (Q t °)))
      ≃⟨ invEquiv Σ-⊎-snd-≃ ⟩
    Σ[ s ∈ S ] (P ₀ s ° × (P ₁ s → T)) ⊎ (Σ[ (p , _) ∈ P ₁ s ° ] Σ[ (_ , t) ∈ (P ₁ s ∖ p → T) × T ] (Q t °))
      ≃⟨ Σ-cong-equiv-snd (λ s → ⊎-right-≃ $ Σ-cong-equiv-snd λ p° → invEquiv $ Σ-cong-equiv-fst $ ungraftEquiv p°) ⟩
    Σ[ s ∈ S ] (P ₀ s ° × (P ₁ s → T)) ⊎ (Σ[ (p , _) ∈ P ₁ s ° ] Σ[ f ∈ (P ₁ s → T) ] (Q (f p) °))
      ≃⟨ Σ-cong-equiv-snd (λ s → ⊎-equiv Σ-swap-≃ Σ-swap-fst-≃) ⟩
    Σ[ s ∈ S ] ((P ₁ s → T) × P ₀ s °) ⊎ (Σ[ f ∈ (P ₁ s → T) ] Σ[ (p , _) ∈ P ₁ s ° ] (Q (f p) °))
      ≃⟨ Σ-cong-equiv-snd (λ s → invEquiv Σ-⊎-snd-≃) ⟩
    Σ[ s ∈ S ] Σ[ f ∈ (P ₁ s → T) ] ((P ₀ s °) ⊎ (Σ[ (p , _) ∈ P ₁ s ° ] (Q (f p) °)))
      ≃∎
      where
        shuffle-right : _ ≃ _
        shuffle-right = strictEquiv
          (λ (((s , p°) , f) , (t , q)) → (s , p° , (f , t) , q))
          (λ (s , p° , (f , t) , q) → (((s , p°) , f) , (t , q)))

  R₁ : 𝟙 → U₁ → Type _
  R₁ i u₁ = L .Pos i (invEq f₁ u₁)

  H₁ : Container _ _
  H₁ .Shape = U₁
  H₁ .Pos = R₁

  U₂ : Type _
  U₂ = Σ[ s ∈ S ] Σ[ f ∈ (P ₁ s → T) ] (P ₀ s °) ⊎ ((Σ[ p ∈ P ₁ s ] Q (f p)) °)

  f₂ : U₂ ≃ (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P ₁ s → T) ] (P ₀ s ⊎ (Σ[ p₁ ∈ P ₁ s ] Q (f p₁))) °)
  f₂ = invEquiv Σ-assoc-≃ ∙ₑ Σ-cong-equiv-snd (λ { (s , f) → invEquiv IsolatedSumEquiv })

  R₂ : 𝟙 → U₂ → Type _
  R₂ i u₂ = R .Pos i (equivFun f₂ u₂)

  H₂ : Container _ _
  H₂ .Shape = U₂
  H₂ .Pos = R₂

  module _ (s : S) (f : P ₁ s → T) where
    η₀ : ((p₀ , _) : P ₀ s °)
      → (P ₀ s ⊎ (Σ[ p₁ ∈ P ₁ s ] Q (f p₁))) ∖ (inl p₀)
          ≃
        ((P ₀ s ∖ p₀) ⊎ (Σ[ p₁ ∈ P ₁ s ] Q (f p₁)))
    η₀ _ = invEquiv remove-left-equiv

    η₁ : ((p₁ , _) : P ₁ s °) ((q , _) : Q (f p₁) °)
      → (P ₀ s ⊎ (Σ[ p ∈ P ₁ s ] Q (f p))) ∖ inr (p₁ , q)
        ≃
        (P ₀ s ⊎ (Σ[ (p , _) ∈ (P ₁ s) ∖ p₁ ] Q (f p))) ⊎ (Q (f p₁) ∖ q)
    η₁ (p₁ , is-isolated-p₁) (q , _)
      =
      (P ₀ s ⊎ (Σ[ p ∈ P ₁ s ] Q (f p))) ∖ inr (p₁ , q)
        ≃⟨ invEquiv remove-right-equiv ⟩
      (P ₀ s ⊎ ((Σ[ p ∈ P ₁ s ] Q (f p)) ∖ (p₁ , q)))
        ≃⟨ ⊎-right-≃ $ invEquiv $ isIsolatedFst→Σ-remove-equiv is-isolated-p₁ ⟩
      P ₀ s ⊎ ((Σ[ (p , _) ∈ (P ₁ s) ∖ p₁ ] Q (f p)) ⊎ (Q (f p₁) ∖ q))
        ≃⟨ invEquiv ⊎-assoc-≃ ⟩
      (P ₀ s ⊎ (Σ[ (p , _) ∈ (P ₁ s) ∖ p₁ ] Q (f p))) ⊎ (Q (f p₁) ∖ q)
        ≃∎

  η : H₁ ⊸ H₂
  η ._⊸_.shape = Σ-map-snd λ s → Σ-map-snd λ f → ⊎-map-right (Σ-isolate (P ₁ s) (Q ∘ f))
  η ._⊸_.pos i (s , f , inl p₀) = η₀ s f p₀
  η ._⊸_.pos i (s , f , inr (p₁ , q)) = η₁ s f p₁ q

  e₁ : Equiv L H₁
  e₁ .Equiv.shape = f₁
  e₁ .Equiv.pos i u₁ = substEquiv' {A = Shape L} (L .Pos i) cancel where
    opaque
      cancel : invEq f₁ (equivFun f₁ u₁) ≡ u₁
      cancel = retEq f₁ u₁

  e₂ : Equiv H₂ R
  e₂ .Equiv.shape = f₂
  e₂ .Equiv.pos i u₂ = idEquiv (Pos H₂ i u₂)

module _ (F : Container ℓ 𝟚) (G : Container ℓ 𝟙) where
  open binary-chain-rule F G

  isContainerEmbeddingChainRule : isContainerEmbedding (binary-chain-rule F G)
  isContainerEmbeddingChainRule = isEmbeddingComp (equivFun f₁) (η ._⊸_.shape ⨟ equivFun f₂)
    (isEquiv→isEmbedding $ equivIsEquiv $ f₁)
    $ isEmbeddingComp (η ._⊸_.shape) (equivFun f₂)
      (isEmbedding-Σ-map-snd λ s →
        isEmbedding-Σ-map-snd λ f →
        isEmbedding-⊎-map-right (Σ-isolate _ _)
        $ isEmbedding-Σ-isolate (P ₁ s) (Q ∘ f)
      )
      (isEquiv→isEmbedding $ equivIsEquiv $ f₂)

  isEquivBinaryChainRule→isEquiv-η : isContainerEquiv (binary-chain-rule F G) → isContainerEquiv η
  isEquivBinaryChainRule→isEquiv-η is-equiv-rule = goal where
    lemma : isContainerEquiv (η ⋆ Equiv.as-⊸ e₂)
    lemma = isContainerEquivCompRight e₁ (η ⋆ Equiv.as-⊸ e₂) is-equiv-rule

    goal : isContainerEquiv η
    goal = isContainerEquivCompLeft η e₂ lemma

  isEquiv-η→isEquiv-Σ-isolate : isContainerEquiv η → (s : S) → (f : P ₁ s → T) → isEquiv (Σ-isolate (P ₁ s) (Q ∘ f))
  isEquiv-η→isEquiv-Σ-isolate is-equiv-η = goal where
    step-1 : (s : S) → isEquiv (Σ-map-snd (λ f → ⊎-map-right (Σ-isolate (P ₁ s) (Q ∘ f))))
    step-1 = isEquiv-Σ-map-snd→isEquiv
      {f = λ s → Σ-map-snd λ f → ⊎-map-right (Σ-isolate (P ₁ s) (Q ∘ f))}
      is-equiv-η

    step-2 : (s : S) (f : P ₁ s → T) → isEquiv (⊎-map-right (Σ-isolate (P ₁ s) (Q ∘ f)))
    step-2 s = isEquiv-Σ-map-snd→isEquiv {f = λ f → ⊎-map-right (Σ-isolate (P ₁ s) (Q ∘ f))} (step-1 s)

    goal : (s : S) (f : P ₁ s → T) → isEquiv (Σ-isolate (P ₁ s) (Q ∘ f))
    goal s f = isEquiv-⊎-map-right→isEquiv _ (step-2 s f)

  isEquivBinaryChainRule→isEquiv-Σ-isolate : isContainerEquiv (binary-chain-rule F G)
    → (s : S) → (f : P ₁ s → T) → isEquiv (Σ-isolate (P ₁ s) (Q ∘ f))
  isEquivBinaryChainRule→isEquiv-Σ-isolate = isEquiv-η→isEquiv-Σ-isolate ∘ isEquivBinaryChainRule→isEquiv-η

  isEquiv-Σ-isolate→isEquivBinaryChainRule :
    ((s : S) → (f : P ₁ s → T) → isEquiv (Σ-isolate (P ₁ s) (Q ∘ f)))
      →
    isContainerEquiv (binary-chain-rule F G)
  isEquiv-Σ-isolate→isEquivBinaryChainRule is-equiv-Σ-isolate = equivIsContainerEquiv binary-chain-rule-equiv where
    η* : H₁ ⧟ H₂
    η* = isContainerEquiv→Equiv η (isEquiv-Σ-map-snd λ s → isEquiv-Σ-map-snd λ f → isEquiv→isEquiv-⊎-map-right (is-equiv-Σ-isolate s f))

    binary-chain-rule-equiv : Equiv _ _
    binary-chain-rule-equiv = e₁ ⋆ₑ η* ⋆ₑ e₂

  isEquivBinaryChainRule≃isEquiv-Σ-isolate :
    isContainerEquiv (binary-chain-rule F G)
      ≃
    ((s : S) → (f : P ₁ s → T) → isEquiv (Σ-isolate (P ₁ s) (Q ∘ f)))
  isEquivBinaryChainRule≃isEquiv-Σ-isolate = propBiimpl→Equiv
    (isPropIsContainerEquiv {f = binary-chain-rule F G})
    (isPropΠ2 λ s f → isPropIsEquiv _)
    isEquivBinaryChainRule→isEquiv-Σ-isolate
    isEquiv-Σ-isolate→isEquivBinaryChainRule

  DiscreteContainer→isEquivBinaryChainRule :
      (∀ s → Discrete (Pos F ₁ s))
    → (∀ t → Discrete (Pos G • t))
    → isContainerEquiv (binary-chain-rule F G)
  DiscreteContainer→isEquivBinaryChainRule disc-F disc-G =
    isEquiv-Σ-isolate→isEquivBinaryChainRule λ s f → Discrete→isEquiv-Σ-isolate (disc-F s) (disc-G ∘ f)
