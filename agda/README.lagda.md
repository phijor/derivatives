<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
module README where

open import Derivative.Prelude
open import Derivative.Basics.Decidable
open import Derivative.Basics.Embedding
open import Derivative.Basics.Equiv
open import Derivative.Basics.Maybe
open import Derivative.Basics.Sum

open import Cubical.Data.Unit.Properties using (isPropUnit*)
open import Cubical.Functions.Surjection
open import Cubical.Categories.Category.Base
open import Cubical.WildCat.Base

private
  variable
    ℓ : Level
    A B : Type ℓ
    a : A
```
-->

# Overview

## Removing Isolated Points in Univalent Foundations

### Isolated points

```agda
open import Derivative.Isolated
```

**Definition 2.1**: Isolated points.
```agda
_ : (a : A) → Type _
_ = isIsolated
```

**Lemma 2.2**: Isolated points have propositional paths.
```agda
_ : (a : A) → isIsolated a → (b : A) → isProp (a ≡ b)
_ = isIsolated→isPropPath
```

**Corollary 2.3**: Being isolated is a proposition.
```agda
_ : (a : A) → isProp (isIsolated a)
_ = isPropIsIsolated
```

**Proposition 2.4**: Isolated points form a set.
```agda
_ : isSet (A °)
_ = isSetIsolated
```

**Lemma 2.5**:
Equivalences preserve and reflect isolated points, hence induce an equivalence.
```agda
_ : (e : A ≃ B) → ∀ a → isIsolated a ≃ isIsolated (equivFun e a)
_ = isIsolated≃isIsolatedEquivFun
```

This induces an equivalence on sets of isolated points:
```agda
_ : (e : A ≃ B) → A ° ≃ B °
_ = IsolatedSubstEquiv
```

**Proposition 2.6**:
Embeddings reflect isolated points.
```agda
_ : (f : A → B) → isEmbedding f → ∀ {a} → isIsolated (f a) → isIsolated a
_ = EmbeddingReflectIsolated
```

**Proposition 2.7**:
The constructors `inl : A → A ⊎ B` and `inr : B → A ⊎ B` preserve and reflect isolated points.
```agda
_ : ∀ {a : A} → isIsolated a ≃ isIsolated (inl {B = B} a)
_ = isIsolated≃isIsolatedInl

_ : ∀ {b : B} → isIsolated b ≃ isIsolated (inr {A = A} b)
_ = isIsolated≃isIsolatedInr
```

**Problem 2.8**:
The above induces an equivalence that distributes isolated points over binary sums:
```agda
_ : (A ⊎ B) ° ≃ (A °) ⊎ (B °)
_ = IsolatedSumEquiv
```

The type `A ⊎ 𝟙` is used so often that we abbreviate it as `Maybe A`:
```agda
_ : (A : Type) → Maybe A ≡ (A ⊎ ⊤ _)
_ = λ A → refl
```

The point `nothing : Maybe A` is always isolated:
```agda
_ : isIsolated {A = Maybe A} nothing
_ = isIsolatedNothing

_ : (Maybe A) °
_ = nothing°
```

**Problem 2.8**:
The isolated points of `Maybe A` are those of `A` or `nothing`:
```agda
_ : (A : Type) → (Maybe A) ° ≃ Maybe (A °)
_ = λ A →
  (Maybe A) °     ≃⟨ IsolatedSumEquiv ⟩
  (A °) ⊎ (⊤ _ °) ≃⟨ ⊎-right-≃ (isProp→IsolatedEquiv isPropUnit*) ⟩
  Maybe (A °)     ≃∎
```

<!--
```agda
module _ (A : Type) (B : A → Type) where
```
-->

**Proposition 2.10**:
There is a map taking (dependent) pairs of isolated points to an
isolated point in the corresponding type of pairs:
```agda
  _ : (Σ[ a° ∈ A ° ] (B (a° .fst)) °) → (Σ[ a ∈ A ] B a) °
  _ = Σ-isolate A B
```

**Proposition 2.11, Proposition 2.12**:
The fibers of this map are propositions, hence it is an embedding.
```agda
  _ : (a : A) (b : B a) (h : isIsolated {A = Σ A B} (a , b))
    → fiber (Σ-isolate A B) ((a , b) , h) ≃ (isIsolated a × isIsolated b)
  _ = Σ-isolate-fiber-equiv A B

  _ : isEmbedding (Σ-isolate A B)
  _ = isEmbedding-Σ-Isolate A B
```

**Lemma 2.13**:
`Σ-isolate` is a surjection (hence equivalence) iff pairing `(_,_)` reflects isolated points.
```agda
  _ : isSurjection (Σ-isolate A B) ≃ (∀ a → (b : B a) → isIsolated {A = Σ A B} (a , b) → isIsolated a × isIsolated b)
  _ = isSurjection-Σ-isolate≃isIsolatedPair A B
```

**Corollary 2.14**:
Over discrete types, `Σ-isolate` is an equivalence.
```agda
  _ : Discrete A → (∀ a → Discrete (B a)) → isEquiv (Σ-isolate A B)
  _ = Discrete→isEquiv-Σ-isolate
```

**Proposition 2.15**:
Over a fixed *isolated* point `a : A`, pairing `λ b → (a , b)` preserves and reflects isolated points.
```agda
  _ : {a₀ : A} → isIsolated a₀ → (b₀ : B a₀) → isIsolated b₀ ≃ isIsolated {A = Σ A B} (a₀ , b₀)
  _ = isIsolatedFst→isIsolatedSnd≃isIsolatedPair
```

**Proposition 2.16**:
Discreteness of a type can be characterized by `Σ-isolate` at the family `B(a) ≔ (a₀ ≡ a)`.
```agda
_ : Discrete A ≃ ((a₀ : A) → isEquiv (Σ-isolate A (a₀ ≡_)))
_ = Discrete≃isEquiv-Σ-isolate-singl
```

### Removing points
```agda
open import Derivative.Remove
```

The type `A ∖ a₀` is the subtype of "`A` with `a₀` removed".
```agda
_ : (A : Type) → (a₀ : A) → (A ∖ a₀) ≡ (Σ[ a ∈ A ] a₀ ≢ a)
_ = λ A a → refl
```

**Problem 2.17**:
Show that first adding a point to `A`, then removing it gives a type equivalent to `A`.
```agda
_ : Maybe A ∖ nothing ≃ A
_ = removeNothingEquiv
```

**Problem 2.18**:
More generally, removing a point from a binary sum is equivalent to
first removing the point from either side, then taking the sum.
```agda
_ : ∀ {a : A} → ((A ∖ a) ⊎ B) ≃ ((A ⊎ B) ∖ (inl a))
_ = remove-left-equiv

_ :  ∀ {b : B} → (A ⊎ (B ∖ b)) ≃ ((A ⊎ B) ∖ (inr b))
_ = remove-right-equiv
```

The other way around there is a map that takes `(A ∖ a₀) ⊎ 𝟙` and replaces `nothing` with `a₀`:
```agda
_ : (a₀ : A) → Maybe (A ∖ a₀) → A
_ = replace
```

**Proposition 2.19**:
The map `replace a₀` is an equivalence if and only if `a₀` is isolated.
```agda
_ : (a₀ : A) → isIsolated a₀ ≃ isEquiv (replace a₀)
_ = isIsolated≃isEquiv-replace
```

<!--
```agda
module _ (A : Type) (B : A → Type) where
```
-->

**Problem 2.20**:
If `a₀` is *h-isolated* (i.e. `isProp (a₀ ≡ a₀)`), then there is a map that
looks like it characterizes removal of points from `Σ`-types.
```agda
  _ : ∀ (a₀ : A) (b₀ : B a₀)
    → (isProp (a₀ ≡ a₀))
    → (Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀) → (Σ A B ∖ (a₀ , b₀))
  _ = Σ-remove
```

**Proposition 2.21**:
If `a₀` is isolated, then it is *h-isolated*, and `Σ-remove a₀ b₀` is an equivalence.
```agda
  _ : ∀ {a₀ : A} {b₀ : B a₀} → (h : isIsolated a₀) → isEquiv (Σ-remove {B = B} a₀ b₀ _)
  _ = isIsolatedFst→isEquiv-Σ-remove
```

### Grafting

**Problem 2.22**:
For all `a : A °`, *grafting* extends the domain a function `f : A ∖ a₀ → B` to all of `A`, given some `b₀ : B`.
```agda
_ : (a° : A °) → (((A ∖° a°) → B) × B) → (A → B)
_ = graft
```

**Problem 2.23**:
This defines an *induction-like* principle for maps out of types `A` pointed by an isolated `a₀ : A °`.
In particular, it has computation rules,
```agda
_ : (a° : A °) (f : (A ∖° a°) → B) {b₀ : B} → graft a° (f , b₀) (a° .fst) ≡ b₀
_ = graft-β-yes

_ : (a° : A °) (f : (A ∖° a°) → B) {b₀ : B} (a : A ∖° a°) → graft a° (f , b₀) (a .fst) ≡ f a
_ = graft-β-no
```

Grafting for dependent functions is defined in:
```agda
import Derivative.Isolated.DependentGrafting
```

??? note
    We do not use this more general definition as it contains an extra `transport`,
    which, for non-dependent functions, is a transport over `refl`.
    Since `transport refl` does not definitionially reduce to the identity function,
    we would have to manually get rid of it everywhere.

## Derivatives of Containers

```agda
open import Derivative.Container
```

**Definition 3.1**:
A container `(S ◁ P)` consists of shapes `S : Type` and over this a family of positions `P : S → Type`.
```agda
_ : (ℓ : Level) → Type (ℓ-suc ℓ)
_ = λ ℓ → Container ℓ ℓ

_ : (S : Type) → (P : S → Type) → Container _ _
_ = λ S P → (S ◁ P)
```

??? note "Universe polymorphism"
    Containers are define for shapes and positions in any universe.
    For most constructions, we consider containers at a fixed level `ℓ`,
    that is the type `Container ℓ ℓ`.
    Some examples consider containers with large shapes (i.e. `Container (ℓ-suc ℓ) ℓ`), but this is mostly for convenience.
    The shapes of those containers could be resized to a type at level `ℓ`.

<!--
```agda
open Container
open Cart
private
  variable
    F G : Container ℓ-zero ℓ-zero
```
-->

**Definition 3.2**:
A (cartesian) morphism of containers consists of a map of shapes,
and a family of equivalences of positions.
```agda
_ : Cart F G ≃ (Σ[ fₛₕ ∈ (F .Shape → G .Shape) ] ∀ s → G .Pos (fₛₕ s) ≃ F .Pos s)
_ = Cart-Σ-equiv
```

**Definition 3.3**:
A morphism is an equivalence of containers if its shape map is an equivalence of types.
We bundle this into a record.
```agda
_ : (F G : Container _ _) → Type ℓ-zero
_ = Equiv
```

Containers and cartesian morphism assemble into a wild category.
Set-truncated containers form a 1-category.
```agda
open import Derivative.Category ℓ-zero

_ : WildCat _ _
_ = ℂont∞

_ : Category _ _
_ = ℂont
```

**Definition 3.4**:
An `(n, k)`-truncated container has `n`-truncated shapes, and `k`-truncated positions.
```agda
_ : (n k : HLevel) → (F : Container _ _) → Type _
_ = isTruncatedContainer {ℓS = ℓ-zero} {ℓP = ℓ-zero}
```

**Lemma 3.5**:
Extensionality for morphisms says that we can compare them by their shape- and position maps.
```agda
_ : (f g : Cart F G)
  → (Σ[ p ∈ f .shape ≡ g .shape ] (PathP (λ i → ∀ s → G .Pos (p i s) ≃ F .Pos s) (f .pos) (g .pos))) ≃ (f ≡ g)
_ = Cart≡Equiv
```

### Derivatives, Universally

```agda
import Derivative.Adjunction
```

### Basic Laws of Derivatives

```agda
import Derivative.Properties
```

## The Chain Rule

```agda
import Derivative.ChainRule
```

## Derivatives of Fixed Points

```agda
import Derivative.Indexed.ChainRule
import Derivative.Indexed.Mu
import Derivative.Indexed.MuRule
```
