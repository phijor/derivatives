{-# OPTIONS --safe #-}
module Derivative.ChainRule where

open import Derivative.Prelude
open import Derivative.Basics.Decidable as Dec
open import Derivative.Basics.Embedding
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

module _ (F G : Container ℓ ℓ) where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  chain-shape-equiv-left :
    ((Σ[ (s , p) ∈ (Σ[ s ∈ S ] (P s °)) ] (P s ∖° p → T)) × (Σ[ t ∈ T ] Q t °))
      ≃
    (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P s → T) ] (Σ[ p° ∈ (P s) ° ] Q (f (p° .fst)) °))
  chain-shape-equiv-left =
    ((Σ[ (s , p°) ∈ (Σ[ s ∈ S ] (P s °)) ] (P s ∖° p° → T)) × (Σ[ t ∈ T ] Q t °))
      ≃⟨ strictEquiv (λ (((s , p°) , f) , t , q°) → ((s , p°) , (f , t) , q°)) (λ ((s , p°) , (f , t) , q°) → (((s , p°) , f) , t , q°)) ⟩
    ((Σ[ (s , p°) ∈ (Σ[ s ∈ S ] (P s °)) ] (Σ[ (_ , t) ∈ (P s ∖° p° → T) × T ] Q t °)))
      ≃⟨ Σ-cong-equiv-snd (λ (s , p°) → invEquiv $ Σ-cong-equiv-fst $ ungraftEquiv p°) ⟩
    ((Σ[ (s , p°) ∈ (Σ[ s ∈ S ] (P s °)) ] (Σ[ f ∈ (P s → T) ] Q (f (p° .fst)) °)))
      ≃⟨ strictEquiv (λ ((s , p°) , (f , q)) → ((s , f) , p° , q)) (λ ((s , f) , p° , q) → ((s , p°) , (f , q))) ⟩
    (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P s → T) ] (Σ[ p° ∈ P s ° ] Q (f (p° .fst)) °))
      ≃∎

  chain-rule : Cart (((∂ F) [ G ]) ⊗ ∂ G) (∂ (F [ G ]))
  chain-rule =
    (((∂ F) [ G ]) ⊗ ∂ G)
      ⊸⟨ Equiv→Cart η₀ ⟩
    H
      ⊸⟨ η₁ ⟩
    (∂ (F [ G ]))
      ⊸∎
    module chain-rule where
      H : Container _ _
      H .Shape = Σ[ (s , f) ∈ Σ[ s ∈ S ] (P s → T) ] (Σ[ p° ∈ (P s) ° ] Q (f (p° .fst)) °)
      H .Pos ((s , f) , (p° , q°)) = (Σ[ (p , _) ∈ P s ∖° p° ] Q (f p)) ⊎ (Q (f (p° .fst)) ∖° q°)

      η₀ : Equiv (((∂ F) [ G ]) ⊗ ∂ G) H
      η₀ = Equiv-inv $ Equiv-fst $ invEquiv chain-shape-equiv-left

      η₁ : Cart H (∂ (F [ G ]))
      η₁ .shape = Σ-map-snd λ (s , f) → Σ-isolate (P s) (Q ∘ f)
      η₁ .pos ((s , f) , (p° , q°)) = invEquiv (isIsolatedFst→Σ-remove-equiv (p° .snd))

  chain-shape-map :
    (Σ[ (s , p) ∈ (Σ[ s ∈ S ] (P s °)) ] (P s ∖ (p .fst) → T)) × (Σ[ t ∈ T ] Q t °)
      →
    (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P s → T) ] (Σ[ p ∈ (P s) ] Q (f p)) °)
  chain-shape-map = chain-rule .shape

  isEmbedding-chain-shape-map : isEmbedding chain-shape-map
  isEmbedding-chain-shape-map = isEmbedding-∘
    {f = Σ-map-snd λ (s , f) → Σ-isolate (P s) (Q ∘ f)}
    {h = equivFun $ chain-rule.η₀ .Equiv.shape}
    (isEmbedding-Σ-map-snd λ (s , f) → isEmbedding-Σ-isolate (P s) (Q ∘ f))
    (isEquiv→isEmbedding $ equivIsEquiv $ chain-rule.η₀ .Equiv.shape)

  isEquivChainRule→isEquiv-Σ-isolated :
    isEquiv (chain-rule .shape) → (∀ s → (f : P s → T) → isEquiv (Σ-isolate (P s) (Q ∘ f)))
  isEquivChainRule→isEquiv-Σ-isolated is-equiv-chain-shape-map = is-equiv-Σ-isolate where
    is-equiv-Σ-Σ-isolate : isEquiv (Σ-map-snd {A = Σ[ s ∈ S ] (P s → T)} (λ (s , f) → Σ-isolate (P s) (Q ∘ f)))
    is-equiv-Σ-Σ-isolate = isEquiv[f∘equivFunA≃B]→isEquiv[f]
      (Σ-map-snd _)
      chain-shape-equiv-left
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

DiscreteContainer : (ℓS ℓP : Level) → Type _
DiscreteContainer ℓS ℓP = Σ[ F ∈ Container ℓS ℓP ] ∀ s → Discrete (F .Pos s)

hasChainEquiv : (ℓ : Level) → Type (ℓ-suc ℓ)
hasChainEquiv ℓ = (F G : Container ℓ ℓ) → isEquiv (chain-shape-map F G)

isPropHasChainEquiv : isProp (hasChainEquiv ℓ)
isPropHasChainEquiv = isPropΠ2 λ F G → isPropIsEquiv _

DiscreteContainer→isEquivChainMap : (F G : DiscreteContainer ℓ ℓ) → isEquiv (chain-shape-map (F .fst) (G .fst))
DiscreteContainer→isEquivChainMap (F , disc-F) (G , disc-G) = isEquiv-Σ-isolated→isEquivChainRule F G is-equiv-Σ-isolate where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  is-equiv-Σ-isolate : ∀ s f → isEquiv (Σ-isolate (P s) (Q ∘ f))
  is-equiv-Σ-isolate s f = Discrete→isEquiv-Σ-isolate (disc-F s) (disc-G ∘ f)

isEquivChainMap→AllTypesDiscrete : hasChainEquiv ℓ → (A : Type ℓ) → Discrete A
isEquivChainMap→AllTypesDiscrete {ℓ} is-equiv-chain-shape-map A = discrete-A where
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

AllTypesDiscrete→isEquivChainMap : ((A : Type ℓ) → Discrete A) → hasChainEquiv ℓ
AllTypesDiscrete→isEquivChainMap discrete F G = DiscreteContainer→isEquivChainMap (F , discrete ∘ Pos F) (G , discrete ∘ Pos G)

isEquivChainMap≃AllTypesDiscrete : hasChainEquiv ℓ ≃ ((A : Type ℓ) → Discrete A)
isEquivChainMap≃AllTypesDiscrete = propBiimpl→Equiv isPropHasChainEquiv (isPropΠ λ A → isPropDiscrete)
  isEquivChainMap→AllTypesDiscrete
  AllTypesDiscrete→isEquivChainMap

¬hasChainEquiv : ¬ hasChainEquiv ℓ-zero
¬hasChainEquiv is-equiv-chain-shape-map = S1.¬isIsolated-base $ Discrete→isIsolated discrete-S¹ base where
  open import Cubical.HITs.S1.Base
  
  discrete-S¹ : Discrete S¹
  discrete-S¹ = isEquivChainMap→AllTypesDiscrete is-equiv-chain-shape-map S¹

isEquivChainMapSets→AllSetsDiscrete :
  ((F G : SetContainer ℓ ℓ) → isEquiv (chain-rule (F .fst) (G .fst) .shape))
    →
  ((A : hSet ℓ) → Discrete ⟨ A ⟩)
isEquivChainMapSets→AllSetsDiscrete {ℓ} is-equiv-chain-shape-map (A , is-set-A) = discrete-A where
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

AllSetsDiscrete→isEquivChainMapSets :
  ((A : hSet ℓ) → Discrete ⟨ A ⟩)
    →
  ((F G : SetContainer ℓ ℓ) → isEquiv (chain-rule (F .fst) (G .fst) .shape))
AllSetsDiscrete→isEquivChainMapSets discrete (F , is-set-F) (G , is-set-G) = DiscreteContainer→isEquivChainMap
  (F , disc-F)
  (G , disc-G)
  where
    disc-F : ∀ s → Discrete (F .Pos s)
    disc-F s = discrete (F .Pos s , is-set-F .snd s)

    disc-G : ∀ t → Discrete (G .Pos t)
    disc-G t = discrete (G .Pos t , is-set-G .snd t)

isEquivChainMapSets≃AllSetsDiscrete :
  ((F G : SetContainer ℓ ℓ) → isEquiv (chain-rule (F .fst) (G .fst) .shape))
    ≃
  ((A : hSet ℓ) → Discrete ⟨ A ⟩)
isEquivChainMapSets≃AllSetsDiscrete = propBiimpl→Equiv
  (isPropΠ2 λ F G → isPropIsEquiv _)
  (isPropΠ λ A → isPropDiscrete)
  isEquivChainMapSets→AllSetsDiscrete
  AllSetsDiscrete→isEquivChainMapSets

impredicativeProp→hasChainEquiv→LEM : (ℓ : Level)
  → (Ω : Type ℓ)
  → (resize : Ω ≃ hProp ℓ)
  → hasChainEquiv ℓ
  → (P : hProp ℓ) → Dec ⟨ P ⟩
impredicativeProp→hasChainEquiv→LEM ℓ Ω resize has-chain-equiv = dec-prop where
  open import Cubical.Relation.Nullary.Properties using (EquivPresDiscrete)

  all-types-discrete : (A : Type ℓ) → Discrete A
  all-types-discrete = isEquivChainMap→AllTypesDiscrete has-chain-equiv

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
