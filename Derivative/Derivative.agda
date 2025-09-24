module Derivative.Derivative where

open import Derivative.Prelude
open import Derivative.Container
open import Derivative.Decidable as Dec
open import Derivative.Isolated
open import Derivative.Remove
open import Derivative.Maybe

open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sum.Base as Sum using (_⊎_ ; inl ; inr)

private
  variable
    ℓ ℓS ℓP : Level

open Container
open Cart


∂ : (F : Container ℓS ℓP) → Container (ℓ-max ℓS ℓP) ℓP
∂ F .Shape = Σ[ s ∈ F .Shape ] (F .Pos s) °
∂ F .Pos (s , p , _) = (F .Pos s) ∖ p

∂[_] : {F G : Container ℓS ℓP} → Cart F G → Cart (∂ F) (∂ G)
∂[_] {F} {G} [ f ◁ u ] = ∂f where
  ∂-shape : (Σ[ s ∈ F .Shape ] F .Pos s °) → (Σ[ t ∈ G .Shape ] G .Pos t °)
  ∂-shape (s , _) .fst = f s
  ∂-shape (s , (p , isolated-p)) .snd .fst = invEq (u s) p
  ∂-shape (s , (p , isolated-p)) .snd .snd = isIsolatedRespectEquiv (u s) p isolated-p

  ∂-pos : (s : F .Shape) (p : F .Pos s °) → (G .Pos (f s) ∖ invEq (u s) (p .fst)) ≃ (F .Pos s ∖ (p .fst))
  ∂-pos s p = RemoveRespectEquiv (p .fst) (u s)

  ∂f : Cart (∂ F) (∂ G)
  ∂f .shape = ∂-shape
  ∂f .pos = uncurry ∂-pos
  {-# INLINE ∂f #-}

module _ (F : Container ℓ ℓ) where
  open Container F renaming (Shape to S ; Pos to P)

  unit-shape : S → Σ[ s ∈ S × ⊤ ℓ ] (P (s .fst) ⊎ (⊤ ℓ)) °
  unit-shape s .fst = s , _
  unit-shape s .snd .fst = nothing
  unit-shape s .snd .snd = isIsolatedNothing

  unit-pos : (s : S) → Maybe (P s) ∖ nothing ≃ P s
  unit-pos s = removeNothingEquiv

  unit : Cart F (∂ (F ⊗Id))
  unit .shape = unit-shape
  unit .pos = unit-pos

module _ (G : Container ℓ ℓ) where
  open Container G renaming (Shape to T ; Pos to Q)
  counit-shape : (Σ[ t ∈ T ] (Q t) °) × (⊤ ℓ) → T
  counit-shape ((t , _ , _) , _) = t

  counit-pos : ∀ (t : T) (q : (Q t)) → isIsolated q → Q t ≃ ((Q t ∖ q) ⊎ ⊤ ℓ)
  counit-pos t q isolated-q = replace-isolated-equiv q isolated-q

  counit : Cart (∂ G ⊗Id) G
  counit .shape = counit-shape
  counit .pos ((t , q , isolated-q) , _) = counit-pos t q isolated-q

is-natural-counit : (F G : Container ℓ ℓ) (f : Cart F G) → [ ∂[ f ] ]⊗Id ⋆ counit G ≡ counit F ⋆ f
is-natural-counit F G f = Cart≡ refl $ funExt λ where
  ((s , p°) , _) → equivEq $ {! !}

∂-Id : Equiv (∂ {ℓS = ℓ} {ℓP = ℓ} Id) Zero
∂-Id .Equiv.shape = Σ-contractFst isContrUnit* ∙ₑ Σ-contractSnd λ { tt* → inhProp→isContr (λ { tt* → yes refl }) (isPropIsIsolated tt*) }
∂-Id .Equiv.pos (tt* , tt* , _) = invEquiv RemoveUnitEquiv

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
  chain-pos s p°@(p₀ , p₀≟_) f t q° =
      ((Σ[ p ∈ P s ] Q (stitch p° (f , t) p)) ∖ (p₀ , subst Q (sym (stitch-β p° f)) (q° .fst)))
        ≃⟨ ? ⟩
      (Σ[ p ∈ P s ] Q' p)
        ≃⟨ ? ⟩
      (Σ[ p ∈ P s ] (Σ[ h ∈ p₀ ≢ p ] Q (f (p , h))) ⊎ ((p₀ ≡ p) × Q t ∖ q° .fst))
        ≃⟨ ? ⟩
      ((Σ[ p ∈ P s ] Σ[ h ∈ p₀ ≢ p ] Q (f (p , h))) ⊎ (singl p₀ × Q t ∖ q° .fst))
        ≃⟨ ? ⟩
      ((Σ[ p ∈ P s ] Σ[ h ∈ p₀ ≢ p ] Q (f (p , h))) ⊎ (Q t ∖ q° .fst))
        ≃⟨ ? ⟩
      ((Σ[ p ∈ P s ∖ p° .fst ] Q (f p)) ⊎ (Q t ∖ q° .fst))
        ≃∎
  -- isoToEquiv λ where
  --     .Iso.fun ((p , q) , neq) → {!q!}
  --     .Iso.inv (inl (p , q)) → (p .fst , {!q!}) , {! !}
  --     .Iso.inv (inr q) → (p° .fst , subst Q (sym (stitch-β p° f)) (q .fst)) , λ eq → {! cong snd eq !}
  --     .Iso.leftInv → {! !}
  --     .Iso.rightInv → {! !}
    where
      f' : P s → T
      f' = stitch p° (f , t)

      Q' : P s → Type _
      Q' p with p₀≟ p
      ... | (yes h) = Q t ∖ q° .fst
      ... | (no ¬h) = Q (f (p , ¬h))
    
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

module _ (F G : Container ℓ ℓ) where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  sum-shape : (Σ[ x ∈ S ⊎ T ] Pos (F ⊕ G) x °) ≃ ((Σ[ s ∈ S ] P s °) ⊎ (Σ[ t ∈ T ] Q t °))
  sum-shape = isoToEquiv λ where
    .Iso.fun (inl s , p) → inl (s , p)
    .Iso.fun (inr t , q) → inr (t , q)
    .Iso.inv (inl (s , p)) → inl s , p
    .Iso.inv (inr (t , q)) → inr t , q
    .Iso.leftInv (inl s , p) → refl
    .Iso.leftInv (inr t , q) → refl
    .Iso.rightInv (inl (s , p)) → refl
    .Iso.rightInv (inr (t , q)) → refl

  sum-rule : Equiv (∂ (F ⊕ G)) (∂ F ⊕ ∂ G)
  sum-rule .Equiv.shape = sum-shape
  sum-rule .Equiv.pos = uncurry (Sum.elim (λ s p → idEquiv (P s ∖ p .fst)) (λ t q → idEquiv (Q t ∖ q .fst)))

module _ (F G : Container ℓ ℓ) where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  prod-shape :
    (Σ[ (s , t) ∈ S × T ] (P s ⊎ Q t) °)
      ≃
    (((Σ[ s ∈ S ] P s °) × T) ⊎ (S × (Σ[ t ∈ T ] Q t °)))
  prod-shape = isoToEquiv λ where
    .Iso.fun ((s , t) , (inl p , iso-p)) → inl ((s , (p , isIsolatedFromInl iso-p)) , t)
    .Iso.fun ((s , t) , (inr q , iso-q)) → inr (s , t , q , isIsolatedFromInr iso-q)
    .Iso.inv (inl ((s , (p , iso-p)) , t)) → (s , t) , inl p , isIsolatedInl iso-p
    .Iso.inv (inr (s , (t , (q , iso-q)))) → (s , t) , inr q , isIsolatedInr iso-q
    .Iso.leftInv ((s , t) , inl p , iso-p) → ΣPathP (refl , Isolated≡ refl)
    .Iso.leftInv ((s , t) , inr q , iso-q) → ΣPathP (refl , Isolated≡ refl)
    .Iso.rightInv (inl ((s , (p , iso-p)) , t)) → cong inl (ΣPathP (ΣPathP (refl , Isolated≡ refl) , refl))
    .Iso.rightInv (inr (s , (t , (q , iso-q)))) → cong inr (ΣPathP (refl , ΣPathP (refl , Isolated≡ refl)))

  prod-rule : Equiv (∂ (F ⊗ G)) ((∂ F ⊗ G) ⊕ (F ⊗ ∂ G))
  prod-rule .Equiv.shape = prod-shape
  prod-rule .Equiv.pos = uncurry λ where
    (s , t) (inl p , iso-p) → {! !}
    (s , t) (inr q , iso-q) → {! !}
