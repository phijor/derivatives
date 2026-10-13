## Fixed Points

<!--
```agda
{-# OPTIONS -WnoUnsupportedIndexedMatch --safe #-}
module Derivative.Parametrized.Mu where

open import Derivative.Parametrized.Container
open import Derivative.Parametrized.Univalence

open import Derivative.Prelude
open import Derivative.Basics.Equiv
open import Derivative.Basics.Function
open import Derivative.Basics.Maybe
open import Derivative.Basics.Sigma
open import Derivative.Basics.Sum
open import Derivative.Basics.W

open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Functions.Embedding

private
  variable
    ℓ : Level
    Ix : Type

open Container
```
-->

The fixpoint container \( \mu F \) is defined in terms of a \( \mathsf{W} \)-type:
For \( F = (S \lhd \vec{P}, P ) \), shapes of \( \mu F \) are \( P \)-branching trees.
```agda
μ : (F : Container ℓ (Maybe Ix)) → Container ℓ Ix
μ {ℓ} {Ix} F = shape ◁ pos module μ where
  open Container F renaming (Shape to S ; Pos to P)

  shape : Type ℓ
  shape = W S (P nothing)

  pos : Ix → shape → Type ℓ
  pos ix = Wᴰ S (P nothing) (P (just ix))
```

\( \mu F \) is a fixpoint of \( F[\_] \):
the containers \( F[ \mu F ] \) and \( \mu F \) are equivalent.
This defines an \( F[\_] \)-algebra, \( \mathsf{in}_F : F[ \mu F ] ⊸ \mu F \).
```agda
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
```

In the other direction, this is a coalgebra \( \mathsf{out}_F : \mu F ⊸ F[ \mu F ] \).
```agda
  μ-out-equiv : Equiv (μ F) (F [ μ F ])
  μ-out-equiv = [ shape ◁≃ pos ] where
    shape : Shape (μ F) ≃ Shape (F [ μ F ])
    shape = W-out-equiv

    pos : ∀ ix s* → Pos (F [ μ F ]) ix (W-out s*) ≃ Pos (μ F) ix s*
    pos ix (sup s f) = Wᴰ-in-equiv _ _ _ s f
    {-# INLINE pos #-}

  μ-out : μ F ⊸ F [ μ F ]
  μ-out = Equiv.as-⊸ μ-out-equiv
```

Of course, both are inverses of each other.
```agda
  μ-in-out : μ-in ⋆ μ-out ≡ id (F [ μ F ])
  μ-in-out = ⊸≡-ext shape-path λ ix (s , f) → funExt (pos-path ix s f) where
    shape-path : W-in ⨟ W-out ≡ idfun _
    shape-path = refl

    pos-path : ∀ ix s
      → (f : P nothing s → W S (P _))
      → (p : (F [ μ F ]) .Pos ix _) → Wᴰ-out S _ _ s f (Wᴰ-in S _ _ s f p) ≡ p
    pos-path ix s f (inl _) = refl
    pos-path ix s f (inr _) = refl
```

The induction principle of \( \mathsf{W} \)-types lets us define a recursor:
any \( F[\_] \)-algebra induces a linear map out of \( \mu F \).
```agda
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
```

We need to prove that its maps on positions are equivalences.
We do so, again, by \( \mathsf{W} \)-induction!
```agda
    pos' : ∀ i → (s : W S (P ₁)) → Q i (shape s) ≃ Pos (μ F) i s
    pos' i (sup s f) =
      Q i (φ.shape (s , shape ∘ f))
        ≃⟨ φ.pos i (s , shape ∘ f) ⟩
      (P (just i) s ⊎ (Σ[ p ∈ P nothing s ] Q i (shape (f p))))
        ≃⟨ ⊎-right-≃ (Σ-cong-equiv-snd λ p → pos' i (f p)) ⟩
      (P (just i) s ⊎ (Σ[ p ∈ P nothing s ] Pos (μ F) i (f p)))
        ≃⟨ Wᴰ-in-equiv S (P nothing) (P (just i)) s f ⟩
      Wᴰ S (P nothing) (P (just i)) (sup s f)
        ≃∎
```

The above conveys that, recursively, the position maps are a composite of three equivalences.
To get slightly better computational behavior, however, we split the construction into two steps:
First define the underlying map by induction, then show (you've guessed it — by induction) that it is an equivalence.
```agda
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
```

The recursor is unique as a coalgebra-to-algebra morphism.
It is obvious that it is *some* coalgebra-to-algebra morphism:
```agda
  module μ-rec-coalgebra-to-algebra (G : Container ℓ Ix) (α : (F [ G ]) ⊸ G) where
    β : μ-rec G α ≡ μ-out ⋆ [-]-map F (μ-rec G α) ⋆ α
    β = ⊸≡-ext (μ-rec.shape-β G α) λ where
      ix (sup s f) → refl
```

To show that it is unique, we reach for the only tool at our disposal:
\( \mathsf{W} \)-induction.
This works out nicely: morphisms out of \( \mu F \) are equivalent to \( \mathsf{W} \)-indexed families.
By function extensionality, it follows that paths (and higher paths) of coalgebra-to-algebra morphisms
are also (equivalent to) \( \mathsf{W} \)-indexed families.
Consequently, we can show that recursion is unique entirely by induction and some path-algebra.
```agda
    unique : isContr (Σ[ α* ∈ μ F ⊸ G ] α* ≡ μ-out ⋆ [-]-map F α* ⋆ α )
    unique .fst .fst = μ-rec G α
    unique .fst .snd = β
```
Given any other map \( \zeta \) that makes the desired square commute,
```agda
    unique .snd (ζ , ζ-β) = ΣPathP (hom-path , hom-square) where
      module α = _⊸_ α
      module ζ = _⊸_ ζ
```
we prove that their shapes agree up to a path.
We remember the paths (\(p, q\)) which we used to construct this:
```agda
      shape-≡-ext : ∀ w → μ-rec.shape G α w ≡ ζ.shape w
      shape-≡-ext w@(sup s f) = p ∙ q
        module shape-≡-ext where
          p = cong α.shape (ΣPathP (refl′ s , funExt (shape-≡-ext ∘ f)))
          q = sym $ cong _⊸_.shape ζ-β ≡$ w

          filler = compPath-filler p q

      shape-≡ : μ-rec.shape G α ≡ ζ.shape
      shape-≡ = funExt shape-≡-ext
```

The paths of positions are obtained by the same (inductive) argument,
except that the composition is now displayed over \( p \) and \( q \).
Again, we remember the paths \( p^D, q^D \) involved.
```agda
      pos-≡-ext : ∀ ix (w : W S (P ₁)) → PathP (λ i → Pos G ix (shape-≡ i w) ≃ μ.pos F ix w) (μ-rec.pos G α ix w) (ζ.pos ix w)
      pos-≡-ext ix (sup s f) = compPathP' {B = B} {p = p} {q = q} pᴰ qᴰ
        module pos-≡ where
          B : Shape G → Type _
          B t = Pos G ix t ≃ μ.pos F ix (sup s f)

          open shape-≡-ext s f using (p ; q)

          yᴰ : _ ≃ _
          yᴰ = α.pos ix (s , ζ.shape ∘ f) ∙ₑ ⊎-right-≃ (Σ-cong-equiv-snd' (ζ.pos ix ∘ f)) ∙ₑ Wᴰ-in-equiv _ _ _ s f

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
```

By extensionality of morphisms, \( \zeta \) agrees with the recursor:
```agda
      hom-path : μ-rec G α ≡ ζ
      hom-path = ⊸≡ shape-≡ pos-≡
```

Both maps are coalgebra-to-algebra morphisms, i.e. they make some squares commute up to some path.
To show that the paths `ζ-β` and `β` agree over the identification `hom-path : μ-rec G α ≡ ζ` that we have just constructed,
we observe the following:
On shapes, `ζ-β` is used to define `hom-path` as a composition of some paths \( p \) and \( q \).
Unfolding this, we obtain a square
```agda
      -- On `w = sup s f`, we observe the following:
      -- * `βₛₕ` is `refl`; this degenerates the left edge.
      -- * on the right, `ζ-βₛₕ` is `sym q` for the path `q` from above.
      -- * at the bottom this is exactly `p`.
      -- * at the top `shape-≡` is p ∙ q.
      --
      --                          p ∙ q = shape-≡
      --    μ-rec.shape w  ∙ ---------------------> ∙  ζ.shape w
      --                   |                        |
      --        βₛₕ = refl |                        | ζ-βₛₕ = sym q
      --                   v                        v
      --    μ-rec.shape w  ∙ ---------------------> ∙  α.shape (s , ζ.shape ∘ f)
      --                               p
      --
      -- This square always has a (unique) filler!
      hom-square-shape : Square {A = W S (P nothing) → Shape G}
        (cong _⊸_.shape β)
        (cong _⊸_.shape ζ-β)
        shape-≡
        λ i z → α.shape (_⊸_.shape ([-]-map F (hom-path i)) (_⊸_.shape μ-out z))
      hom-square-shape i j (sup s f) = shape-≡-ext.filler s f (~ j) i
```
This serves as our desired filler on shapes.

With a little bit of work (but following the same idea),
we see that the same is true on positions.
```agda
      hom-square-pos-ext : ∀ ix w
        → SquareP (λ i j → Pos G ix (hom-square-shape i j w) ≃ μ.pos F ix w)
          (λ i → β i ._⊸_.pos ix w)
          (λ i → ζ-β i ._⊸_.pos ix w)
          (λ i → pos-≡-ext ix w i)
          λ i → (α.pos ix (_⊸_.shape ([-]-map F (hom-path i)) (_⊸_.shape μ-out w))) ∙ₑ (_⊸_.pos ([-]-map F (hom-path i)) ix (_⊸_.shape μ-out w) ∙ₑ _⊸_.pos μ-out ix w)
      hom-square-pos-ext ix (sup s f) = equivSquareP λ i j → equivFun (pos-≡.filler ix s f (~ j) i)

      hom-square-pos : SquareP (λ i j → ∀ ix w → Pos G ix (hom-square-shape i j w) ≃ μ.pos F ix w)
        (cong _⊸_.pos β)
        (cong _⊸_.pos ζ-β)
        pos-≡
        λ i ix w → (α.pos ix (_⊸_.shape ([-]-map F (hom-path i)) (_⊸_.shape μ-out w))) ∙ₑ (_⊸_.pos ([-]-map F (hom-path i)) ix (_⊸_.shape μ-out w) ∙ₑ _⊸_.pos μ-out ix w)
      hom-square-pos i j ix w = hom-square-pos-ext ix w i j
```

Together, we see that both commutative squares agree:
```agda
      hom-square : Square β ζ-β hom-path (cong (λ f → μ-out ⋆ [-]-map F f ⋆ α) hom-path)
      hom-square i j ._⊸_.shape = hom-square-shape i j
      hom-square i j ._⊸_.pos = hom-square-pos i j
```

Since equivalences of containers are an identity system,
we can equivalently reshape the coalgebra-to-algebra square to an \( F[\_] \)-algebra square:
canceling `μ-in` and `μ-out` is an equivalence.
Hence, maps out of \( \mu F \) are unique, and it forms the initial \( F[\_] \)-algebra.
```agda
  opaque
    μ-rec-unique : (G : Container ℓ Ix)
      → (α : (F [ G ]) ⊸ G)
      → isContr (Σ[ α* ∈ μ F ⊸ G ] μ-in ⋆ α* ≡ [-]-map F α* ⋆ α )
    μ-rec-unique G α = isOfHLevelRespectEquiv 0 (Σ-cong-equiv-snd comm-square-equiv)
      $ μ-rec-coalgebra-to-algebra.unique G α
      where module _ (α* : μ F ⊸ G) where
        cancel : μ-in ⋆ (μ-out ⋆ ([-]-map F α* ⋆ α)) ≡ [-]-map F α* ⋆ α
        cancel =
          μ-in ⋆ (μ-out ⋆ ([-]-map F α* ⋆ α))
            ≡⟨ sym (⋆-assoc μ-in μ-out ([-]-map F α* ⋆ α)) ⟩
          (μ-in ⋆ μ-out) ⋆ ([-]-map F α* ⋆ α)
            ≡⟨ cong (_⋆ ([-]-map F α* ⋆ α)) μ-in-out ⟩
          id (F [ μ F ]) ⋆ ([-]-map F α* ⋆ α)
            ≡⟨ ⋆-id-left _ ⟩
          [-]-map F α* ⋆ α
            ∎

        comm-square-equiv : (α* ≡ μ-out ⋆ [-]-map F α* ⋆ α) ≃ (μ-in ⋆ α* ≡ [-]-map F α* ⋆ α)
        comm-square-equiv =
          (α* ≡ (μ-out ⋆ [-]-map F α*) ⋆ α)
            ≃⟨ compPathrEquiv (⋆-assoc μ-out ([-]-map F α*) α) ⟩
          (α* ≡ μ-out ⋆ ([-]-map F α* ⋆ α))
            ≃⟨ congEquiv (containerEquivPreCompEquiv μ-in-equiv G) ⟩
          (μ-in ⋆ α* ≡ μ-in ⋆ (μ-out ⋆ ([-]-map F α* ⋆ α)))
            ≃⟨ compPathrEquiv cancel ⟩
          (μ-in ⋆ α* ≡ [-]-map F α* ⋆ α)
            ≃∎
```

We did not compute this directly, but it follows that `μ-rec` has a computation rule:
```agda
    μ-rec-β : (G : Container ℓ Ix)
      → (α : (F [ G ]) ⊸ G)
      → μ-in ⋆ μ-rec G α ≡ [-]-map F (μ-rec G α) ⋆ α
    μ-rec-β G α = μ-rec-unique G α .fst .snd
```

Two important (and immediate) consequences of this construction are the following.
First, the recursor reflects fixpoints:
```agda
  isEquivFrom-μ-rec : (G : Container ℓ Ix)
    → (φ : (F [ G ]) ⊸ G)
    → isContainerEquiv (μ-rec G φ)
    → isContainerEquiv φ
  isEquivFrom-μ-rec G φ is-equiv-μ-rec = is-equiv-φ where
    open μ-rec-coalgebra-to-algebra G φ using (β)
    is-equiv-comp : isContainerEquiv (μ-out ⋆ [-]-map F (μ-rec G φ) ⋆ φ)
    is-equiv-comp = subst isContainerEquiv β is-equiv-μ-rec

    is-equiv-μ-out⋆F[μ-rec] : isContainerEquiv (μ-out ⋆ [-]-map F (μ-rec G φ))
    is-equiv-μ-out⋆F[μ-rec] = isContainerEquivComp
      μ-out
      ([-]-map F (μ-rec G φ))
      (equivIsContainerEquiv μ-out-equiv)
      (isEquiv-[-]-map F (μ-rec G φ) is-equiv-μ-rec)

    is-equiv-φ : isContainerEquiv φ
    is-equiv-φ = isContainerEquivCompRight' (μ-out ⋆ [-]-map F (μ-rec G φ)) φ is-equiv-μ-out⋆F[μ-rec] is-equiv-comp
```

Second, it preserves container embeddings.
In some sense, it is also a least pre-fixpoint with respect to embeddings:
if \( F[G] \leq G \), then \( \mu F \leq G \).
```agda
  isEmbedding-μ-rec : (G : Container ℓ Ix)
    → (α : (F [ G ]) ⊸ G)
    → isContainerEmbedding α
    → isContainerEmbedding (μ-rec G α)
  isEmbedding-μ-rec G α = goal where
    module α = _⊸_ α

    goal : isEmbedding α.shape → isEmbedding (W-rec α.shape)
    goal = isEmbedding-W-rec α.shape
```
