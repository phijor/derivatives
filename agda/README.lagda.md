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

private
  variable
    ℓ : Level
    A B : Type ℓ
    a : A
```
-->

# Removing Isolated Points in Univalent Foundations

## Isolated points

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

## Removing points
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

# Derivatives of Containers

```agda
import Derivative.Container
```

## Derivatives, Universally

```agda
import Derivative.Adjunction
```

## Basic Laws of Derivatives

```agda
import Derivative.Properties
```

# The Chain Rule

```agda
import Derivative.ChainRule
```

# Derivatives of Fixed Points

```agda
import Derivative.Indexed.ChainRule
import Derivative.Indexed.Mu
import Derivative.Indexed.MuRule
```
