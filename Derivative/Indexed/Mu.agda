-- TODO: Clean up imports
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Derivative.Indexed.Mu where

open import Derivative.Indexed.Container
open import Derivative.Indexed.Derivative
open import Derivative.Indexed.ChainRule

open import Derivative.Prelude
open import Derivative.Decidable
open import Derivative.Isolated
open import Derivative.Maybe
open import Derivative.Remove
open import Derivative.Square
open import Derivative.Sum
open import Derivative.W

open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport using (substEquiv)
import      Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
import      Cubical.Data.Unit as Unit
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

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
    {-# INLINE pos #-}

  μ-out : μ F ⊸ F [ μ F ]
  μ-out = Equiv.as-⊸ μ-out-equiv

  μ-rec-Π : (G : Container ℓ Ix)
    → (F [ G ]) Π⊸ G
    → μ F Π⊸ G
  μ-rec-Π G α = W-elim goal where
    module _ (s : S) (f : P nothing s → W S (P nothing)) where
      goal : (∀ p → Σ[ t ∈ G .Shape ] ∀ ix → Pos G ix t ≃ Pos (μ F) ix (f p))
        → Σ[ t ∈ G .Shape ] ∀ ix → Pos G ix t ≃ Pos (μ F) ix (sup s f)
      goal rec .fst = α (s , fst ∘ rec) .fst
      goal rec .snd = λ ix → α (s , fst ∘ rec) .snd ix ∙ₑ ⊎-right-≃ (Σ-cong-equiv-snd λ p → rec p .snd ix) ∙ₑ Wᴰ-in-equiv _ _ _ s f

  μ-rec : (G : Container ℓ Ix)
    → (F [ G ]) ⊸ G
    → μ F ⊸ G
  μ-rec G φ = [ shape ⊸ pos ] module μ-rec where
    open Container G renaming (Shape to T ; Pos to Q)

    module φ = _⊸_ φ

    shape : W S (P nothing) → T
    shape = W-rec φ.shape

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

    pos : ∀ i → (s : W S (P ₁)) → Q i (shape s) ≃ Pos (μ F) i s
    pos i w .fst = pos-fun i w
    pos i w .snd = is-equiv-pos-fun i w
    {-# INLINE pos #-}

    pos' : ∀ i → (s : W S (P ₁)) → Q i (shape s) ≃ Pos (μ F) i s
    pos' i (sup s f) =
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

  -- TODO: Prove directly that μ-rec is unique by reshaping the type of algebra-morphisms
  isProp-rec-unique' : (G : Container ℓ Ix) (α : (F [ G ]) ⊸ G) → isProp (Σ[ α* ∈ μ F ⊸ G ] α* ≡ μ-out ⋆ [-]-map F α* ⋆ α)
  isProp-rec-unique' G α@([ f ⊸ u ]) = isOfHLevelRespectEquiv 1 (invEquiv equiv) {! !} where
    rec-pos :
      ∀ (u* : ∀ (ix : Ix) (w : W S (P ₁)) → Pos G ix (W-rec f w) ≃ Wᴰ _ _ (Pos F (just ix)) w)
      → ∀ (ix : Ix) (w : W S (P ₁)) → Pos G ix ((W-out ⨟ Σ-map-snd (λ z → _∘_ (W-rec f)) ⨟ f) w) ≃ Wᴰ S (P ₁) (P (just ix)) w
    rec-pos u* = (μ-out ⋆ [-]-map F (the (μ F ⊸ G) ([ W-rec f ⊸ u* ])) ⋆ α) ._⊸_.pos

    RHS : (μ F ⊸ G) → (μ F ⊸ G)
    RHS α*@([ f* ⊸ u* ]) = μ-out ⋆ [-]-map F α* ⋆ α where
      _ = {! equivFun $ (μ-out ⋆ [-]-map F α* ⋆ α) ._⊸_.pos _ _ !}
    RHS-pos : ∀ ix (w : W S (P ₁))
      → (f* : W _ _ → Shape G)
      → (u* : Pos G ix (f* w) → Wᴰ _ _ (P (just ix)) w)
      → Pos G ix (f* w) → Wᴰ _ _ (P (just ix)) w
    -- RHS-pos ix (sup s x) f* u* = Wᴰ-in _ _ _ s x ∘ {! ⊎-map-right !} ∘ u*
    RHS-pos ix (sup s x) f* u* = Wᴰ-in _ _ _ s x ∘ {!  !} ∘ u*

    equiv : (Σ[ α* ∈ μ F ⊸ G ] α* ≡ μ-out ⋆ [-]-map F α* ⋆ α ) ≃ {! !}
    equiv =
      (Σ[ α* ∈ μ F ⊸ G ] α* ≡ μ-out ⋆ [-]-map F α* ⋆ α)
        ≃⟨ Σ-cong-equiv-fst ⊸-Σ-equiv ⟩
      (Σ[ (f* , u*) ∈ Σ[ f* ∈ (W _ _ → Shape G) ] (∀ ix w → Pos G ix (f* w) ≃ Wᴰ _ _ (Pos F (just ix)) w) ] [ f* ⊸ u* ] ≡ RHS ([ f* ⊸ u* ]))
        ≃⟨ strictEquiv (λ { ((f* , u*) , p) → (f* , cong _⊸_.shape p) , (u* , cong _⊸_.pos p) }) (λ { ((f* , pˢ) , (u* , pᵖ)) → ((f* , u*) , λ i → [ pˢ i ⊸ pᵖ i ]) }) ⟩
      Σ[ (f* , h) ∈ Σ[ f* ∈ (W S _ → Shape G) ] f* ≡ W-out ⨟ Σ-map-snd (λ _ → f* ∘_) ⨟ f ] Σ[ u* ∈ (∀ ix w → Pos G ix (f* w) ≃ Wᴰ _ _ (Pos F (just ix)) w) ] PathP (λ i → ∀ ix w → Pos G ix (h i w) ≃ Wᴰ _ _ (P (just ix)) w) u* (RHS ([ f* ⊸ u* ]) ._⊸_.pos)
        ≃⟨ Σ-contractFst (W-out-unique f) ⟩
      Σ[ u* ∈ (∀ ix w → Pos G ix (W-rec f w) ≃ Wᴰ _ _ (Pos F (just ix)) w) ] PathP (λ i → ∀ ix w → Pos G ix (W-rec-β f i w) ≃ Wᴰ _ _ (P (just ix)) w) u* (RHS [ W-rec f ⊸ u* ] ._⊸_.pos)
        ≃⟨ invEquiv $ Σ-cong-equiv-snd (λ u* → funExt₂Equiv) ⟩
      Σ[ u* ∈ (∀ ix w → Pos G ix (W-rec f w) ≃ Wᴰ _ _ (Pos F (just ix)) w) ]
        (∀ ix (w : W S _) → PathP (λ i → Pos G ix (W-rec-β f i w) ≃ Wᴰ _ _ (P (just ix)) w) (u* ix w) (RHS [ W-rec f ⊸ u* ] ._⊸_.pos ix w))
        ≃⟨ Σ-cong-equiv-snd (λ u* → equivΠCod λ ix → equivΠCod λ w → invEquiv equivPathPEquiv) ⟩
      Σ[ u* ∈ (∀ ix w → Pos G ix (W-rec f w) ≃ Wᴰ _ _ (Pos F (just ix)) w) ]
        (∀ ix (w : W S _) → PathP (λ i → Pos G ix (W-rec-β f i w) → Wᴰ _ _ (P (just ix)) w) (equivFun $ u* ix w) (equivFun $ RHS [ W-rec f ⊸ u* ] ._⊸_.pos ix w))
        ≃⟨ Σ-cong-equiv-snd (λ u* → equivΠCod λ ix → equivΠ' W-out-equiv λ p → {! !}) ⟩
      Σ[ u* ∈ (∀ ix w → Pos G ix (W-rec f w) ≃ Wᴰ _ _ (Pos F (just ix)) w) ]
        (∀ ix ((s , x) : Σ _ _)
          → PathP (λ i → Pos G ix (f (s , (λ p → W-rec f (x p)))) → Wᴰ _ _ (P (just ix)) (sup s x))
            (equivFun $ u* ix (sup s x))
            {! !}
        )
        -- ≃⟨ invEquiv (Σ-Π₂-≃ {A = Ix} {B = λ _ → W S _} {C = λ ix w → Pos G ix (W-rec f w) ≃ Wᴰ _ _ (Pos F (just ix)) w} {D = λ ix w u* → {! !}}) ⟩
      -- (∀ ix (w : W S _) → Σ[ u* ∈ Pos G ix (W-rec f w) ≃ Wᴰ _ _ (Pos F (just ix)) w ] PathP (λ i → Pos G ix (W-rec-β f i w) → Wᴰ _ _ (P (just ix)) w) (equivFun u*) _)
        -- ≃⟨ equivΠCod (λ ix → equivΠCod λ w → Σ-cong-equiv-snd λ u* → invEquiv equivPathPEquiv) ⟩
      -- (∀ ix (w : W S _) → Σ[ u* ∈ Pos G ix (W-rec f w) ≃ Wᴰ _ _ (Pos F (just ix)) w ] PathP (λ i → Pos G ix (W-rec-β f i w) → Wᴰ _ _ (P (just ix)) w) (equivFun u*) _)
        -- ≃⟨ {! Σ-Π-≃ !} ⟩
        ≃⟨ {! !} ⟩
      {! !}
        ≃∎

    contr : ∀ ix → (w : W S (P nothing)) → ∃![ u* ∈ Pos G ix (W-rec f w) ≃ Wᴰ _ _ (Pos F (just ix)) w ] PathP (λ i → Pos G ix (W-rec-β f i w) → Wᴰ _ _ (P (just ix)) w) (equivFun u*) _
    contr ix (sup s f) = {! !}

  μ-rec-unique' : (G : Container ℓ Ix)
    → (α : (F [ G ]) ⊸ G)
    → isContr (Σ[ α* ∈ μ F ⊸ G ] α* ≡ μ-out ⋆ [-]-map F α* ⋆ α )
  μ-rec-unique' G α .fst .fst = μ-rec G α
  μ-rec-unique' G α .fst .snd = μ-rec-β' G α
  μ-rec-unique' G α .snd (ζ , ζ-β) = ΣPathP (goal , goal-coh) where
    module α = _⊸_ α
    module ζ = _⊸_ ζ

    shape-≡-ext : ∀ w → μ-rec.shape G α w ≡ ζ.shape w
    shape-≡-ext w@(sup s f) = p ∙ q
      module shape-≡-ext where
        p = cong α.shape (ΣPathP (refl′ s , funExt (shape-≡-ext ∘ f)))
        q = sym $ cong _⊸_.shape ζ-β ≡$ w

        filler = compPath-filler p q

    shape-≡ : μ-rec.shape G α ≡ ζ.shape
    shape-≡ = funExt shape-≡-ext

    pos-≡-ext : ∀ ix (w : W S (P ₁)) → PathP (λ i → Pos G ix (shape-≡ i w) ≃ μ.pos F ix w) (μ-rec.pos G α ix w) (ζ.pos ix w)
    pos-≡-ext ix (sup s f) = compPathP' {B = B} {p = p} {q = q} pᴰ qᴰ
      module pos-≡ where
        B : Shape G → Type _
        B t = Pos G ix t ≃ μ.pos F ix (sup s f)

        open shape-≡-ext s f using (p ; q)

        yᴰ : _ ≃ _
        yᴰ = α.pos ix (s , ζ.shape ∘ f) ∙ₑ ⊎-right-≃ (Σ-cong-equiv-snd (ζ.pos ix ∘ f)) ∙ₑ Wᴰ-in-equiv _ _ _ s f

        pᴰ-fun : PathP (λ i → Pos G ix (shape-≡-ext.p s f i) → μ.pos F ix (sup s f)) (equivFun $ μ-rec.pos G α ix (sup s f)) (equivFun yᴰ)
        pᴰ-fun i =
          equivFun (α.pos ix (s , shape-≡ i ∘ f))
          ⨟ᴰ ⊎-map-right (Σ-map-snd {B = λ p₁ → Pos G ix (shape-≡ i (f p₁))} λ p₁ → equivFun (pos-≡-ext ix (f p₁) i))
          ⨟ᴰ Wᴰ-in _ _ _ s f

        pᴰ : PathP (λ i → B (shape-≡-ext.p s f i)) (μ-rec.pos G α ix (sup s f)) yᴰ
        pᴰ = equivPathP pᴰ-fun

        qᴰ : PathP (λ i → B (shape-≡-ext.q s f i)) yᴰ (ζ.pos ix (sup s f))
        qᴰ i = ζ-β (~ i) ._⊸_.pos ix (sup s f)

        filler : SquareP (λ z i → B (compPath-filler p q z i)) pᴰ (compPathP' {B = B} {p = p} {q = q} pᴰ qᴰ) _ qᴰ
        filler = compPathP'-filler {B = B} {p = p} {q = q} pᴰ qᴰ

    pos-≡ : PathP (λ i → ∀ ix w → Pos G ix (shape-≡ i w) ≃ μ.pos F ix w) (μ-rec.pos G α) ζ.pos
    pos-≡ = funExt₂ pos-≡-ext

    goal : μ-rec G α ≡ ζ
    goal = ⊸≡ shape-≡ pos-≡

    goal-coh-shape : Square {A = W S (P nothing) → Shape G}
      (λ i → μ-rec-β' G α i ._⊸_.shape)
      (λ i → ζ-β i ._⊸_.shape)
      shape-≡
      λ i z → α.shape (_⊸_.shape ([-]-map F (goal i)) (_⊸_.shape μ-out z))
    goal-coh-shape i j (sup s f) = shape-≡-ext.filler s f (~ j) i

    goal-coh-pos-ext : ∀ ix w
      → SquareP (λ i j → Pos G ix (goal-coh-shape i j w) ≃ μ.pos F ix w)
        (λ i → μ-rec-β' G α i ._⊸_.pos ix w)
        (λ i → ζ-β i ._⊸_.pos ix w)
        (λ i → pos-≡-ext ix w i)
        λ i → (α.pos ix (_⊸_.shape ([-]-map F (goal i)) (_⊸_.shape μ-out w))) ∙ₑ (_⊸_.pos ([-]-map F (goal i)) ix (_⊸_.shape μ-out w) ∙ₑ _⊸_.pos μ-out ix w)
    goal-coh-pos-ext ix (sup s f) = equivSquareP λ i j → equivFun (pos-≡.filler ix s f (~ j) i)

    goal-coh-pos : SquareP (λ i j → ∀ ix w → Pos G ix (goal-coh-shape i j w) ≃ μ.pos F ix w)
      (λ i → μ-rec-β' G α i ._⊸_.pos)
      (λ i → ζ-β i ._⊸_.pos)
      pos-≡
      λ i ix w → (α.pos ix (_⊸_.shape ([-]-map F (goal i)) (_⊸_.shape μ-out w))) ∙ₑ (_⊸_.pos ([-]-map F (goal i)) ix (_⊸_.shape μ-out w) ∙ₑ _⊸_.pos μ-out ix w)
    goal-coh-pos i j ix w = goal-coh-pos-ext ix w i j

    goal-coh : Square (μ-rec-β' G α) ζ-β goal (cong (λ f → μ-out ⋆ [-]-map F f ⋆ α) goal)
    goal-coh i j ._⊸_.shape = goal-coh-shape i j
    goal-coh i j ._⊸_.pos = goal-coh-pos i j

  opaque
    μ-rec-unique : (G : Container ℓ Ix)
      → (α : (F [ G ]) ⊸ G)
      → isContr (Σ[ α* ∈ μ F ⊸ G ] μ-in ⋆ α* ≡ [-]-map F α* ⋆ α )
    μ-rec-unique G α = isOfHLevelRespectEquiv 0 (Σ-cong-equiv-snd comm-square-equiv) $ μ-rec-unique' G α
      where
        μ-out-inv-coh : Equiv.as-⊸ (Equiv.inv μ-out-equiv) ≡ μ-in
        μ-out-inv-coh = ⊸≡-ext
          (refl′ (uncurry sup))
          λ ix (s , f) → funExt λ wᴰ → transportRefl _ ∙ transportRefl (Wᴰ-out S (P ₁) (P (just ix)) s f wᴰ)

        comm-square-equiv : (α* : μ F ⊸ G) → (α* ≡ μ-out ⋆ [-]-map F α* ⋆ α) ≃ (μ-in ⋆ α* ≡ [-]-map F α* ⋆ α)
        comm-square-equiv α* =
          (α* ≡ (μ-out ⋆ [-]-map F α*) ⋆ α)
            ≃⟨ compPathrEquiv (⋆-assoc μ-out ([-]-map F α*) α) ⟩
          (α* ≡ μ-out ⋆ ([-]-map F α* ⋆ α))
            ≃⟨ containerAdjointEquiv μ-out-equiv α* ([-]-map F α* ⋆ α) ⟩
          (Equiv.as-⊸ (Equiv.inv μ-out-equiv) ⋆ α* ≡ [-]-map F α* ⋆ α)
            ≃⟨ substEquiv (λ - → - ⋆ α* ≡ [-]-map F α* ⋆ α) μ-out-inv-coh ⟩
          (μ-in ⋆ α* ≡ [-]-map F α* ⋆ α)
            ≃∎

    μ-rec-β : (G : Container ℓ Ix)
      → (α : (F [ G ]) ⊸ G)
      → μ-in ⋆ μ-rec G α ≡ [-]-map F (μ-rec G α) ⋆ α
    μ-rec-β G α = μ-rec-unique G α .fst .snd

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

  isEmbedding-μ-rec : (G : Container ℓ Ix)
    → (α : (F [ G ]) ⊸ G)
    → isEmbedding (α ._⊸_.shape)
    → isEmbedding (μ-rec G α ._⊸_.shape)
  isEmbedding-μ-rec G α = {! !} where
    module α = _⊸_ α

    step₁ : isEmbedding (([-]-map F (μ-rec G α) ⋆ α) ._⊸_.shape)
    step₁ = {! !}

    goal : isEmbedding (W-rec α.shape)
    goal = {! !}

  isSurjection-μ-rec : (G : Container ℓ Ix)
    → (α : (F [ G ]) ⊸ G)
    → isSurjection (α ._⊸_.shape)
    → isSurjection (μ-rec G α ._⊸_.shape)
  isSurjection-μ-rec G α = {! !} where
    step₁ : isSurjection (([-]-map F (μ-rec G α) ⋆ α) ._⊸_.shape)
    step₁ = {! !}
