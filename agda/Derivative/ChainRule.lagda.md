<!--
```agda
{-# OPTIONS --safe #-}
module Derivative.ChainRule where

open import Derivative.Prelude
open import Derivative.Basics.Decidable as Dec
open import Derivative.Basics.Embedding
open import Derivative.Basics.Function
open import Derivative.Basics.Sigma
open import Derivative.Basics.Sum as Sum using (_⊎_ ; inl ; inr)
open import Derivative.Basics.Unit

open import Derivative.Container
open import Derivative.Derivative
open import Derivative.Isolated
import      Derivative.Isolated.S1 as S1
open import Derivative.Remove

open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Path using (congPathIso)
open import Cubical.Foundations.Transport using (substEquiv ; isSet-subst ; subst⁻)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary.HLevels using (isPropDiscrete)

private
  variable
    ℓ ℓS ℓP : Level

open Container
open Cart
```
-->

# The chain rule

For any pair of containers, we can define a cartesian morphism
`chain-rule : ∂ F [ G ] ⊗ ∂ G ⊸ ∂ (F [ G ])`, a _lax_ chain rule.
Under some circumstances, this morphism will be invertible,
that is a _strong_ chain rule.
```agda
module _ (F G : Container ℓ ℓ) where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)
  chain-rule : Cart (∂ F [ G ] ⊗ ∂ G) (∂ (F [ G ]))
```

The chain rule is defined by first using [`ungraftEquiv`](Derivative.Isolated.Grafting.html#ungraftEquiv)
to adjust shapes and positions via an equivalence of containers (`η₀`),
and then distributing isolated points over Σ-types by means of [`Σ-isolate`](Derivative.Isolated.Sigma.html#Σ-isolate) (`η₁`).
```agda
  chain-rule =
    ∂ F [ G ] ⊗ ∂ G
      ⊸⟨ Equiv→Cart η₀ ⟩
    H
      ⊸⟨ η₁ ⟩
    ∂ (F [ G ])
      ⊸∎
    module chain-rule where
      equiv-left :
        (Σ[ (s , p) ∈ Σ[ s ∈ S ] (P s °) ] (P s ∖° p → T)) × (Σ[ t ∈ T ] Q t °)
          ≃
        (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P s → T) ] Σ[ p° ∈ (P s) ° ] Q (f (p° .fst)) °)
      equiv-left =
        (Σ[ (s , p°) ∈ (Σ[ s ∈ S ] (P s °)) ] (P s ∖° p° → T)) × (Σ[ t ∈ T ] Q t °)
          ≃⟨ step-I ⟩
        Σ[ (s , p°) ∈ Σ[ s ∈ S ] (P s °) ] Σ[ (_ , t) ∈ (P s ∖° p° → T) × T ] Q t °
          ≃⟨ Σ-cong-equiv-snd (λ (s , p°) → invEquiv $ Σ-cong-equiv-fst $ ungraftEquiv p°) ⟩
        Σ[ (s , p°) ∈ Σ[ s ∈ S ] (P s °) ] Σ[ f ∈ (P s → T) ] Q (f (p° .fst)) °
          ≃⟨ step-II ⟩
        Σ[ (s , f) ∈ Σ[ s ∈ S ] (P s → T) ] Σ[ p° ∈ P s ° ] Q (f (p° .fst)) °
          ≃∎ where
          step-I = strictEquiv
            (λ (((s , p°) , f) , t , q°) → ((s , p°) , (f , t) , q°))
            (λ ((s , p°) , (f , t) , q°) → (((s , p°) , f) , t , q°))
          step-II = strictEquiv
            (λ ((s , p°) , (f , q)) → ((s , f) , p° , q))
            (λ ((s , f) , p° , q) → ((s , p°) , (f , q)))

      H : Container _ _
      H .Shape = Σ[ (s , f) ∈ Σ[ s ∈ S ] (P s → T) ] Σ[ p° ∈ (P s) ° ] Q (f (p° .fst)) °
      H .Pos ((s , f) , (p° , q°)) = (Σ[ (p , _) ∈ P s ∖° p° ] Q (f p)) ⊎ (Q (f (p° .fst)) ∖° q°)

      η₀ : Equiv (∂ F [ G ] ⊗ ∂ G) H
      η₀ = Equiv-inv $ Equiv-fst $ invEquiv equiv-left

      η₁ : Cart H (∂ (F [ G ]))
      η₁ .shape = Σ-map-snd λ (s , f) → Σ-isolate (P s) (Q ∘ f)
      η₁ .pos ((s , f) , (p° , q°)) = invEquiv (isIsolatedFst→Σ-remove-equiv (p° .snd))
```

The map of shapes of the chain rule is always an embedding.
```agda
  chain-shape-map :
    (Σ[ (s , p) ∈ Σ[ s ∈ S ] (P s °) ] (P s ∖ (p .fst) → T)) × (Σ[ t ∈ T ] Q t °)
      →
    Σ[ (s , f) ∈ Σ[ s ∈ S ] (P s → T) ] (Σ[ p ∈ (P s) ] Q (f p)) °
  chain-shape-map = chain-rule .shape

  isEmbedding-chain-shape-map : isEmbedding chain-shape-map
  isEmbedding-chain-shape-map = isEmbedding-∘
    {f = Σ-map-snd λ (s , f) → Σ-isolate (P s) (Q ∘ f)}
    {h = equivFun $ chain-rule.η₀ .Equiv.shape}
    (isEmbedding-Σ-map-snd λ (s , f) → isEmbedding-Σ-isolate (P s) (Q ∘ f))
    (isEquiv→isEmbedding $ equivIsEquiv $ chain-rule.η₀ .Equiv.shape)
```

It is an equivalence of shapes if and only if `Σ-isolate (P s) (Q ∘ f)` is an equivalence.
```agda
  isEquivChainRule→isEquiv-Σ-isolated :
    isEquiv (chain-rule .shape) → (∀ s → (f : P s → T) → isEquiv (Σ-isolate (P s) (Q ∘ f)))
  isEquivChainRule→isEquiv-Σ-isolated is-equiv-chain-shape-map = is-equiv-Σ-isolate where
    is-equiv-Σ-Σ-isolate : isEquiv (Σ-map-snd {A = Σ[ s ∈ S ] (P s → T)} (λ (s , f) → Σ-isolate (P s) (Q ∘ f)))
    is-equiv-Σ-Σ-isolate = isEquiv[f∘equivFunA≃B]→isEquiv[f]
      (Σ-map-snd _)
      chain-rule.equiv-left
      is-equiv-chain-shape-map

    is-equiv-Σ-isolate : ∀ s f → isEquiv (Σ-isolate (P s) (Q ∘ f))
    is-equiv-Σ-isolate = curry $ isEquiv-Σ-map-snd→isEquiv is-equiv-Σ-Σ-isolate

  isEquiv-Σ-isolated→isEquivChainRule :
    (∀ s → (f : P s → T) → isEquiv (Σ-isolate (P s) (Q ∘ f)))
      →
    isEquiv (chain-rule .shape)
  isEquiv-Σ-isolated→isEquivChainRule is-equiv-Σ-isolate = isEquiv-∘
    {f = equivFun $ chain-rule.η₀ .Equiv.shape}
    {g = Σ-map-snd λ ((s , f)) → Σ-isolate (P s) (Q ∘ f)}
    (isEquiv-Σ-map-snd $ uncurry is-equiv-Σ-isolate)
    (equivIsEquiv $ chain-rule.η₀ .Equiv.shape)

  isEquivChainRule≃isEquiv-Σ-isolated :
    isEquiv (chain-rule .shape) ≃ (∀ s → (f : P s → T) → isEquiv (Σ-isolate (P s) (Q ∘ f)))
  isEquivChainRule≃isEquiv-Σ-isolated = propBiimpl→Equiv
    (isPropIsEquiv _) (isPropΠ2 λ s f → isPropIsEquiv _)
    isEquivChainRule→isEquiv-Σ-isolated
    isEquiv-Σ-isolated→isEquivChainRule
```

The chain rule is _strong_ if it is an equivalence of containers,
that is, whenever its shape map is an equivalence.
```agda
isStrong : (F G : Container ℓ ℓ) → Type _
isStrong F G = isEquiv (chain-shape-map F G)
```

It is _globally strong_ if this is the case for any choice of containers.
```agda
isGloballyStrong : (ℓ : Level) → Type (ℓ-suc ℓ)
isGloballyStrong ℓ = (F G : Container ℓ ℓ) → isStrong F G

isPropIsGloballyStrong : isProp (isGloballyStrong ℓ)
isPropIsGloballyStrong = isPropΠ2 λ F G → isPropIsEquiv _
```

For discrete containers, the chain rule is strong.
```agda
DiscreteContainer→isStrong : (F G : DiscreteContainer ℓ ℓ) → isStrong (F .fst) (G .fst)
DiscreteContainer→isStrong (F , disc-F) (G , disc-G) = isEquiv-Σ-isolated→isEquivChainRule F G is-equiv-Σ-isolate where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  is-equiv-Σ-isolate : ∀ s f → isEquiv (Σ-isolate (P s) (Q ∘ f))
  is-equiv-Σ-isolate s f = Discrete→isEquiv-Σ-isolate (disc-F s) (disc-G ∘ f)
```

Having a globally strong chain rule is an inconsistent assumption.
A globally strong chain rule is equivalent to assuming that any _type_ is discrete.
```agda
isGloballyStrong→AllTypesDiscrete : isGloballyStrong ℓ → (A : Type ℓ) → Discrete A
isGloballyStrong→AllTypesDiscrete {ℓ} is-equiv-chain-shape-map A = discrete-A where
  F : Container ℓ ℓ
  F .Shape = 𝟙*
  F .Pos _ = A

  G : (a₀ : A) → Container ℓ ℓ
  G a₀ .Shape = A
  G a₀ .Pos = a₀ ≡_

  is-equiv-Σ-isolate-singl : (a₀ : A) → isEquiv (Σ-isolate A (a₀ ≡_))
  is-equiv-Σ-isolate-singl a₀ = isEquivChainRule→isEquiv-Σ-isolated F (G a₀)
    (is-equiv-chain-shape-map F (G a₀))
    •
    (idfun A)

  discrete-A : Discrete A
  discrete-A = isEquiv-Σ-isolate-singl→Discrete is-equiv-Σ-isolate-singl

AllTypesDiscrete→isGloballyStrong : ((A : Type ℓ) → Discrete A) → isGloballyStrong ℓ
AllTypesDiscrete→isGloballyStrong discrete F G = DiscreteContainer→isStrong (F , discrete ∘ Pos F) (G , discrete ∘ Pos G)

isGloballyStrong≃AllTypesDiscrete : isGloballyStrong ℓ ≃ ((A : Type ℓ) → Discrete A)
isGloballyStrong≃AllTypesDiscrete = propBiimpl→Equiv isPropIsGloballyStrong (isPropΠ λ A → isPropDiscrete)
  isGloballyStrong→AllTypesDiscrete
  AllTypesDiscrete→isGloballyStrong
```

Of course, there are non-discrete types (for example, the circle `S¹`),
hence a globally strong chain rule cannot hold.
```agda
¬isGloballyStrong : ¬ isGloballyStrong ℓ-zero
¬isGloballyStrong is-equiv-chain-shape-map = S1.¬isIsolated-base $ Discrete→isIsolated discrete-S¹ base where
  open import Cubical.HITs.S1.Base
  
  discrete-S¹ : Discrete S¹
  discrete-S¹ = isGloballyStrong→AllTypesDiscrete is-equiv-chain-shape-map S¹
```

Restricted to _h_-sets, the assumption is less strong:
The chain rule is strong for all set-truncated containers
if and only if all _h_-sets are discrete.
```agda
isStrongSets→AllSetsDiscrete :
  ((F G : SetContainer ℓ ℓ) → isStrong (F .fst) (G .fst))
    →
  ((A : hSet ℓ) → Discrete ⟨ A ⟩)
isStrongSets→AllSetsDiscrete {ℓ} is-equiv-chain-shape-map (A , is-set-A) = discrete-A where
  F : SetContainer ℓ ℓ
  F .fst .Shape = 𝟙*
  F .fst .Pos _ = A
  F .snd .fst = isSet-𝟙*
  F .snd .snd _ = is-set-A

  G : (a₀ : A) → SetContainer ℓ ℓ
  G a₀ .fst .Shape = A
  G a₀ .fst .Pos = a₀ ≡_
  G a₀ .snd .fst = is-set-A
  G a₀ .snd .snd a = isOfHLevelPath 1 (is-set-A a₀ a)

  is-equiv-Σ-isolate-singl : (a₀ : A) → isEquiv (Σ-isolate A (a₀ ≡_))
  is-equiv-Σ-isolate-singl a₀ = isEquivChainRule→isEquiv-Σ-isolated _ _
    (is-equiv-chain-shape-map F (G a₀))
    •
    (idfun A)

  discrete-A : Discrete A
  discrete-A = isEquiv-Σ-isolate-singl→Discrete is-equiv-Σ-isolate-singl

AllSetsDiscrete→isStrongSets :
  ((A : hSet ℓ) → Discrete ⟨ A ⟩)
    →
  ((F G : SetContainer ℓ ℓ) → isEquiv (chain-rule (F .fst) (G .fst) .shape))
AllSetsDiscrete→isStrongSets discrete (F , is-set-F) (G , is-set-G) = DiscreteContainer→isStrong
  (F , disc-F)
  (G , disc-G)
  where
    disc-F : ∀ s → Discrete (F .Pos s)
    disc-F s = discrete (F .Pos s , is-set-F .snd s)

    disc-G : ∀ t → Discrete (G .Pos t)
    disc-G t = discrete (G .Pos t , is-set-G .snd t)

isStrongSets≃AllSetsDiscrete :
  ((F G : SetContainer ℓ ℓ) → isEquiv (chain-rule (F .fst) (G .fst) .shape))
    ≃
  ((A : hSet ℓ) → Discrete ⟨ A ⟩)
isStrongSets≃AllSetsDiscrete = propBiimpl→Equiv
  (isPropΠ2 λ F G → isPropIsEquiv _)
  (isPropΠ λ A → isPropDiscrete)
  isStrongSets→AllSetsDiscrete
  AllSetsDiscrete→isStrongSets
```

In the presences of a small replacement `Ω` of `hProp`,
a strong chain rule for _h_-sets would let us decide arbitrary propositions (a form of LEM).
```agda
impredicativeProp→isGloballyStrong→LEM : (ℓ : Level)
  → (Ω : Type ℓ)
  → (resize : Ω ≃ hProp ℓ)
  → isGloballyStrong ℓ
  → (P : hProp ℓ) → Dec ⟨ P ⟩
impredicativeProp→isGloballyStrong→LEM ℓ Ω resize has-chain-equiv = dec-prop where
  open import Cubical.Relation.Nullary.Properties using (EquivPresDiscrete)

  all-types-discrete : (A : Type ℓ) → Discrete A
  all-types-discrete = isGloballyStrong→AllTypesDiscrete has-chain-equiv

  Ω-discrete : Discrete Ω
  Ω-discrete = all-types-discrete Ω

  hProp-discrete : Discrete (hProp ℓ)
  hProp-discrete = EquivPresDiscrete resize Ω-discrete

  𝟙ᴾ : hProp ℓ
  𝟙ᴾ .fst = 𝟙*
  𝟙ᴾ .snd _ _ = refl

  dec-equal-𝟙 : (P : hProp ℓ) → Dec (P ≡ 𝟙ᴾ)
  dec-equal-𝟙 P = hProp-discrete P 𝟙ᴾ

  dec-prop : ∀ P → Dec ⟨ P ⟩
  dec-prop P = Dec.map
    (λ P≡𝟙 → subst ⟨_⟩ (sym P≡𝟙) •)
    (λ P≢𝟙 p → P≢𝟙 $ Σ≡Prop (λ _ → isPropIsProp) (isContr→≡𝟙* (inhProp→isContr p (str P))))
    (dec-equal-𝟙 P)
```
