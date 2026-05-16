<!--
```agda
{-# OPTIONS --safe #-}
module Derivative.Bag where

open import Derivative.Prelude
open import Derivative.Container
open import Derivative.Derivative
open import Derivative.Isolated
open import Derivative.Remove
open import Derivative.Basics.Decidable as Dec
open import Derivative.Basics.Maybe

open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary using (isProp¬)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (inl ; inr ; _⊎_)
open import Cubical.Data.FinSet.Constructors
```
-->

# Bags (finite multisets) are a ∂-fixpoint

```agda
open import Cubical.Data.FinSet as FinSet renaming (FinSet to FinSet*)
open import Cubical.Data.FinSet.Induction as Fin renaming (_+_ to _+ᶠ_) hiding (𝟙)
private
  FinSet = FinSet* ℓ-zero
```

## The `Bag` container

We define a container `Bag` representing finite multisets.
Its shapes are the (large) _h_-groupoid of of finite sets,
i.e. types merely equivalent to some standard finite type `Fin n`.
Over a finite set `X : FinSet`, the type of positions is simply the underlying type `⟨ X ⟩ : Type`.
```agda
Bag : Container (ℓ-suc ℓ-zero) ℓ-zero
Bag .Container.Shape = FinSet
Bag .Container.Pos = ⟨_⟩
```

`Bag` is a symmetric container: the type of finite sets is an _h_-groupoid,
and positions are a family of _h_-sets.
```agda
isSymmetricContainer : isTruncatedContainer h-groupoid h-set Bag
isSymmetricContainer .fst = isGroupoidFinSet
isSymmetricContainer .snd X = isFinSet→isSet (str X)
```

## Operations on finite sets

For any finite set `X`, the type  `X ∖ x` is a decidable subtype, hence a finite set.
```agda
isFinSetMinus : ∀ {X : Type} → isFinSet X → ∀ x → isFinSet (X ∖ x)
isFinSetMinus {X} is-finset-X x = isFinSetΣ (X , is-finset-X) λ x′ → (¬ x ≡ x′) , is-finset-≢ x′
  where
    is-finset-≢ : ∀ x′ → isFinSet (x ≢ x′)
    is-finset-≢ x′ = isDecProp→isFinSet (isProp¬ _) (decNot (isFinSet→Discrete is-finset-X x x′))
```

This extends to an operation on finite sets.
```agda
_-ᶠ_ : (X : FinSet) → (x : ⟨ X ⟩) → FinSet
(X -ᶠ x) .fst = ⟨ X ⟩ ∖ x
(X -ᶠ x) .snd = isFinSetMinus (str X) x
```

For pointed finite sets, this defines a "predecessor" operation that removes the chosen point.
```agda
FinSet• : Type₁
FinSet• = Σ[ X ∈ FinSet ] ⟨ X ⟩

pred : FinSet• → FinSet
pred (X , x) = X -ᶠ x
```

The unit type is obviously finite,
```agda
𝟙ᶠ : FinSet
```
<!--
```agda
𝟙ᶠ .fst = 𝟙
𝟙ᶠ .snd .fst = 1
𝟙ᶠ .snd .snd = PT.∣ isoToEquiv iso ∣₁ where
    iso : Iso 𝟙 (_ ⊎ _)
    iso .Iso.fun _ = just _
    iso .Iso.inv (inl _) = _
    iso .Iso.inv (inr ())
    iso .Iso.rightInv (inl _) = refl
    iso .Iso.rightInv (inr ())
    iso .Iso.leftInv _ = refl
```
-->

and we can always point a finite set by adding one:
```agda
succ : FinSet → FinSet•
succ X .fst = X +ᶠ 𝟙ᶠ
succ X .snd = nothing
```

Finite sets have decidable equality, hence all their points are isolated.
```agda
isIsolatedFin : ∀ {X : FinSet} (x₀ : ⟨ X ⟩) → isIsolated x₀
isIsolatedFin {X} = Discrete→isIsolated (isFinSet→Discrete (str X))

IsolatedFinEquiv : (X : FinSet) → ⟨ X ⟩ ° ≃ ⟨ X ⟩
IsolatedFinEquiv (X , is-finset) = Discrete→IsolatedEquiv $ isFinSet→Discrete {A = X} is-finset
```

This is enough to show that together, [`pred`](#pred) and [`succ`](#succ) form an isomorphism between finite- and pointed, finite sets:
```agda
pred-iso : Iso FinSet• FinSet
pred-iso .Iso.fun = pred
pred-iso .Iso.inv = succ
pred-iso .Iso.rightInv X = equivFun (FinSet≡ _ _) $ ua $ fin-equiv where
  fin-equiv : (⟨ X +ᶠ 𝟙ᶠ ⟩ ∖ nothing) ≃ ⟨ X ⟩
  fin-equiv = removeNothingEquiv
pred-iso .Iso.leftInv (X , x₀) = ΣPathP λ where
    .fst → fin-path
    .snd → pt-path
  where
    fin-equiv : ⟨ (X -ᶠ x₀) +ᶠ 𝟙ᶠ ⟩ ≃ ⟨ X ⟩
    fin-equiv = replace-isolated-equiv x₀ (isIsolatedFin {X = X} x₀)

    fin-path : (X -ᶠ x₀) +ᶠ 𝟙ᶠ ≡ X
    fin-path = equivFun (FinSet≡ _ _) $ ua fin-equiv

    pt-path : PathP (λ i → ⟨ fin-path i ⟩) nothing x₀
    pt-path = ua-gluePath fin-equiv $ refl′ x₀
```

## The ∂-fixpoint

The shapes of `∂ Bag` are pointed finite sets, hence [`pred`](#pred) induces an equivalence with the shapes of `Bag`:
```agda
∂-shape-equiv : (Σ[ X ∈ FinSet ] (⟨ X ⟩ °)) ≃ FinSet
∂-shape-equiv =
  Σ[ X ∈ FinSet ] ⟨ X ⟩ °
    ≃⟨ Σ-cong-equiv-snd IsolatedFinEquiv ⟩
  FinSet•
    ≃⟨ isoToEquiv pred-iso ⟩
  FinSet
    ≃∎
```

By definition, `_-ᶠ_` is just removal of (isolated) points of a finite set.
In particular, this is an equivalence between the positions of `Bag` and those of `∂ Bag`.
```agda
∂-pos-equiv : (X : FinSet) (x : ⟨ X ⟩ °) → (⟨ X ⟩ ∖° x) ≃ ⟨ X -ᶠ (forget-isolated x) ⟩
∂-pos-equiv X x = idEquiv _
```

Together, these define an equivalence of the containers `∂ Bag` and `Bag`.
```agda
∂-Bag-equiv : Equiv (∂ Bag) Bag
∂-Bag-equiv .Equiv.shape = ∂-shape-equiv
∂-Bag-equiv .Equiv.pos = uncurry ∂-pos-equiv
```

### Fixpoints of ±-closed universes

The argument above does apply to _any_ subuniverse of types specified by a predicate
`P : Type → hProp`, as long as `P` is closed under addition and removal of single points.
```agda
module Universe (P : Type → Type)
  (is-prop-P : ∀ A → isProp (P A))
  (is-P-+1 : ∀ {A : Type} → P A → P (A ⊎ 𝟙))
  (is-P-∖ : ∀ {A : Type} → P A → (a : A °) → P (A ∖° a))
  where
  U : Type₁
  U = Σ[ X ∈ Type ] P X

  uBag : Container (ℓ-suc ℓ-zero) ℓ-zero
  uBag .Container.Shape = U
  uBag .Container.Pos = ⟨_⟩

  _-ᵁ_ : (X : U) → (x : ⟨ X ⟩ °) → U
  (X -ᵁ x) .fst = ⟨ X ⟩ ∖° x
  (X -ᵁ x) .snd = is-P-∖ (str X) x

  _+1 : U → U
  (X +1) .fst = ⟨ X ⟩ ⊎ 𝟙
  (X +1) .snd = is-P-+1 (str X)

  ∂-uBag-shape-Iso : Iso (Σ[ X ∈ U ] (⟨ X ⟩ °)) U
  ∂-uBag-shape-Iso .Iso.fun (X , x) = X -ᵁ x
  ∂-uBag-shape-Iso .Iso.inv X .fst = X +1
  ∂-uBag-shape-Iso .Iso.inv X .snd = nothing°
  ∂-uBag-shape-Iso .Iso.rightInv X = Σ≡Prop is-prop-P $ ua $ removeNothingEquiv
  ∂-uBag-shape-Iso .Iso.leftInv (X , x°@(x₀ , isolated-x₀)) = ΣPathP (U-path , pt-path) where
    U-equiv : (⟨ X ⟩ ∖ x₀) ⊎ 𝟙 ≃ ⟨ X ⟩
    U-equiv = replace-isolated-equiv x₀ isolated-x₀

    U-path : (X -ᵁ x°) +1 ≡ X
    U-path = Σ≡Prop is-prop-P $ ua U-equiv

    pt-path : PathP (λ i → ⟨ U-path i ⟩ °) nothing° x°
    pt-path = IsolatedPathP {B = ⟨_⟩} {p = U-path} (ua-gluePath U-equiv (refl′ x₀))

  ∂-uBag-shape : (Σ[ X ∈ U ] (⟨ X ⟩ °)) ≃ U
  ∂-uBag-shape = isoToEquiv ∂-uBag-shape-Iso

  ∂-uBag : Equiv (∂ uBag) uBag
  ∂-uBag .Equiv.shape = ∂-uBag-shape
  ∂-uBag .Equiv.pos (X , x) = idEquiv ⟨ X -ᵁ x ⟩
```

### Sub-countable types

An example of the above are sub-countable types, i.e. those that merely embed into ℕ.
These define a container representing multisets with cardinality of at most ℵ₀.
```agda
module SubNat where
  open import Cubical.Data.Nat
  open import Cubical.Functions.Embedding

  isSub : (X : Type) → Type _
  isSub X = ∥ X ↪ ℕ ∥₁

  isPropIsSub : ∀ X → isProp (isSub X)
  isPropIsSub X = isPropPropTrunc

  isSub-⊤ : isSub 𝟙
  isSub-⊤ = PT.∣ const 0 , hasPropFibers→isEmbedding (λ { n (• , _) (• , _) → Σ≡Prop (λ _ → isSetℕ _ _) refl }) ∣₁

  isSub-+1 : ∀ {X} → isSub X → isSub (X ⊎ 𝟙)
  isSub-+1 {X} = PT.map _+1 where module _ (ι : X ↪ ℕ) where
    suc-ι : (X ⊎ 𝟙) → ℕ
    suc-ι (just x) = suc (ι .fst x)
    suc-ι nothing = 0

    _+1 : (X ⊎ 𝟙) ↪ ℕ
    _+1 .fst = suc-ι
    _+1 .snd = injEmbedding isSetℕ cancel where
      cancel : ∀ {x y : X ⊎ 𝟙} → suc-ι x ≡ suc-ι y → x ≡ y
      cancel {x = just x} {y = just y} p = cong just (isEmbedding→Inj (ι .snd) x y (injSuc p))
      cancel {x = just x} {y = nothing} = ex-falso ∘ snotz
      cancel {x = nothing} {y = just y} = ex-falso ∘ znots
      cancel {x = nothing} {y = nothing} _ = refl′ nothing

  isSub-∖ : ∀ {X} → isSub X → ∀ x → isSub (X ∖° x)
  isSub-∖ {X} = PT.rec (isPropΠ λ x → isPropIsSub (X ∖° x)) λ ι (x , _) → PT.∣ compEmbedding ι (forget-remove-embedding x) ∣₁

  open Universe isSub isPropIsSub isSub-+1 isSub-∖
    renaming (uBag to ℕBag)

  ∂-ℕBag : Equiv (∂ ℕBag) ℕBag
  ∂-ℕBag = ∂-uBag
```
