module Derivative.ChainRule where

open import Derivative.Prelude
open import Derivative.Container
open import Derivative.Decidable as Dec
open import Derivative.Derivative
open import Derivative.Isolated
open import Derivative.Remove
open import Derivative.Sum as Sum using (_⊎_ ; inl ; inr)

open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Path using (congPathIso)
open import Cubical.Foundations.Transport using (substEquiv ; isSet-subst ; subst⁻)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

private
  variable
    ℓ ℓS ℓP : Level

open Container
open Cart

module _ (F G : Container ℓ ℓ) where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  chain-shape-equiv-left :
    ((Σ[ (s , p) ∈ (Σ[ s ∈ S ] (P s °)) ] (P s ∖ (p .fst) → T)) × (Σ[ t ∈ T ] Q t °))
      ≃
    (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P s → T) ] (Σ[ p° ∈ (P s) ° ] Q (f (p° .fst)) °))
  chain-shape-equiv-left =
    ((Σ[ (s , p°) ∈ (Σ[ s ∈ S ] (P s °)) ] (P s ∖ (p° .fst) → T)) × (Σ[ t ∈ T ] Q t °))
      ≃⟨ strictEquiv (λ (((s , p°) , f) , t , q°) → ((s , p°) , (f , t) , q°)) (λ ((s , p°) , (f , t) , q°) → (((s , p°) , f) , t , q°)) ⟩
    ((Σ[ (s , p°) ∈ (Σ[ s ∈ S ] (P s °)) ] (Σ[ (_ , t) ∈ (P s ∖ (p° .fst) → T) × T ] Q t °)))
      ≃⟨ Σ-cong-equiv-snd (λ (s , p°) → invEquiv $ Σ-cong-equiv-fst $ unstitchEquiv p°) ⟩
    ((Σ[ (s , p°) ∈ (Σ[ s ∈ S ] (P s °)) ] (Σ[ f ∈ (P s → T) ] Q (f (p° .fst)) °)))
      ≃⟨ strictEquiv (λ ((s , p°) , (f , q)) → ((s , f) , p° , q)) (λ ((s , f) , p° , q) → ((s , p°) , (f , q))) ⟩
    (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P s → T) ] (Σ[ p° ∈ P s ° ] Q (f (p° .fst)) °))
      ≃∎

  chain-map :
    (Σ[ (s , p) ∈ (Σ[ s ∈ S ] (P s °)) ] (P s ∖ (p .fst) → T)) × (Σ[ t ∈ T ] Q t °)
      →
    (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P s → T) ] (Σ[ p ∈ (P s) ] Q (f p)) °)
  chain-map =
    _ →≃⟨ chain-shape-equiv-left ⟩
    _ →⟨ Σ-map-snd (λ (s , f) → Σ-isolate (P s) (Q ∘ f)) ⟩
    _ →∎

  chain-pos : (s : S) (p° : P s °) (f : P s ∖ p° .fst → T) (t : T) (q° : Q t °)
    →
      ((Σ[ p ∈ P s ] Q (stitch p° (f , t) p)) ∖ (p° .fst , subst Q (sym (stitch-β p° f)) (q° .fst)))
        ≃
      ((Σ[ p ∈ P s ∖ p° .fst ] Q (f p)) ⊎ (Q t ∖ q° .fst))
  chain-pos s p°@(p₀ , p₀≟_) f t q°@(q₀ , q₀≟_) =
      ((Σ[ p ∈ P s ] Q (f' p)) ∖ (p₀ , subst Q (sym (stitch-β p° f)) q₀))
        ≃⟨ invEquiv (isIsolatedFst→Σ-remove-equiv p₀≟_) ⟩
      (Σ[ (p , _) ∈ P s ∖ p₀ ] Q (f' p)) ⊎ (Q (f' p₀) ∖ subst Q (sym $ stitch-β (p₀ , p₀≟_) f) q₀)
        ≃⟨ Sum.⊎-equiv (Σ-cong-equiv-snd subst-I) (Σ-cong-equiv subst-II neq-III) ⟩
      ((Σ[ (p , h) ∈ P s ∖ p₀ ] Q (f (p , h))) ⊎ (Q t ∖ q₀))
        ≃∎
    where
      f' : P s → T
      f' = stitch p° (f , t)

      subst-I : ((p , h) : P s ∖ p₀) → Q (f' p) ≃ Q (f (p , h))
      subst-I p' = substEquiv Q (stitch-β' p° f p')
    
      subst-II : Q (f' p₀) ≃ Q t
      subst-II = substEquiv Q (stitch-β p° f)

      neq-III : (q : Q (f' p₀)) → (subst⁻ Q (stitch-β p° f) q₀ ≢ q) ≃ (q₀ ≢ subst Q (stitch-β p° f) q)
      neq-III q = neqCongEquiv $ substAdjointEquiv Q (sym $ stitch-β p° f) {x′ = q₀} {y′ = q}
    
  chain-rule : Cart (((∂ F) [ G ]) ⊗ ∂ G) (∂ (F [ G ]))
  chain-rule .Cart.shape = chain-map
  chain-rule .pos (((s , p°) , f) , t , q°) = chain-pos s p° f t q°

DiscreteContainer : (ℓS ℓP : Level) → Type _
DiscreteContainer ℓS ℓP = Σ[ F ∈ Container ℓS ℓP ] ∀ s → Discrete (F .Pos s)

hasChainEquiv : (ℓ : Level) → Type (ℓ-suc ℓ)
hasChainEquiv ℓ = (F G : Container ℓ ℓ) → isEquiv (chain-map F G)

DiscreteContainer→isEquivChainMap : (F G : DiscreteContainer ℓ ℓ) → isEquiv (chain-map (F .fst) (G .fst))
DiscreteContainer→isEquivChainMap (F , disc-F) (G , disc-G) = equivIsEquiv chain-equiv where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  chain-equiv :
    (Σ[ (s , p) ∈ (Σ[ s ∈ S ] (P s °)) ] (P s ∖ (p .fst) → T)) × (Σ[ t ∈ T ] Q t °)
      ≃
    (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P s → T) ] (Σ[ p ∈ (P s) ] Q (f p)) °)
  chain-equiv =
    _ ≃⟨ chain-shape-equiv-left F G ⟩
    _ ≃⟨ Σ-map-snd (λ (s , f) → Σ-isolate (P s) (Q ∘ f)) , isEquiv-Σ-map-snd (λ (s , f) → Discrete→isEquiv-Σ-isolate (disc-F s) (disc-G ∘ f)) ⟩
    _ ≃∎

isEquivChainMap→AllTypesDiscrete : hasChainEquiv ℓ → (A : Type ℓ) → Discrete A
isEquivChainMap→AllTypesDiscrete {ℓ} is-equiv-chain-map A = discrete-A where
  lemma : (F G : Container ℓ ℓ) → (s : F .Shape) (f : F .Pos s → G .Shape) → isEquiv (Σ-isolate (F .Pos s) (G .Pos ∘ f))
  lemma F G = is-equiv-Σ-isolate where
    open Container F renaming (Shape to S ; Pos to P)
    open Container G renaming (Shape to T ; Pos to Q)

    is-equiv-Σ-Σ-isolate : isEquiv (Σ-map-snd {A = Σ[ s ∈ S ] (P s → T)} (λ (s , f) → Σ-isolate (P s) (Q ∘ f)))
    is-equiv-Σ-Σ-isolate = isEquiv[f∘equivFunA≃B]→isEquiv[f]
      (Σ-map-snd _)
      (chain-shape-equiv-left F G)
      (is-equiv-chain-map F G)

    is-equiv-Σ-isolate : ∀ s f → isEquiv (Σ-isolate (P s) (Q ∘ f))
    is-equiv-Σ-isolate = curry $ isEquiv-Σ-map-snd→isEquiv is-equiv-Σ-Σ-isolate

  F : Container ℓ ℓ
  F .Shape = Unit*
  F .Pos _ = A

  G : (B : A → Type ℓ) → Container ℓ ℓ
  G B .Shape = A
  G B .Pos = B

  is-equiv-Σ-isolate : ∀ B → isEquiv (Σ-isolate A B)
  is-equiv-Σ-isolate B = lemma F (G B) tt* (λ a → a)

  discrete-A : Discrete A
  discrete-A = isEquiv-Σ-isolate→DiscreteFst A is-equiv-Σ-isolate

¬hasChainEquiv : ¬ hasChainEquiv ℓ-zero
¬hasChainEquiv is-equiv-chain-map = S1.¬isIsolated-base $ Discrete→isIsolated discrete-S¹ base where
  open import Cubical.HITs.S1.Base
  
  discrete-S¹ : Discrete S¹
  discrete-S¹ = isEquivChainMap→AllTypesDiscrete is-equiv-chain-map S¹
