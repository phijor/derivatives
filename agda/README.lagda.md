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

private
  variable
    ℓ : Level
    A B : Type ℓ
    a : A
```
-->

# Removing Isolated Points in Univalent Foundations

```agda
open import Derivative.Isolated
```

Definition 2.1: Isolated points.
```agda
_ : (a : A) → Type _
_ = isIsolated
```

Lemma 2.2: Isolated points have propositional paths.
```agda
_ : (a : A) → isIsolated a → (b : A) → isProp (a ≡ b)
_ = isIsolated→isPropPath
```

Corollary 2.3: Being isolated is a proposition.
```agda
_ : (a : A) → isProp (isIsolated a)
_ = isPropIsIsolated
```

Proposition 2.4: Isolated points form a set.
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
