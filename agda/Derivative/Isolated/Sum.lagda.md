<!--
```agda
{-# OPTIONS --safe #-}
module Derivative.Isolated.Sum where

open import Derivative.Prelude
open import Derivative.Isolated.Base

open import Derivative.Basics.Decidable as Dec
open import Derivative.Basics.Sum as Sum using (_⊎_ ; inl ; inr)

private
  variable
    ℓ : Level
    A B : Type ℓ
```
-->

# Isolated points of sum types

Since both `inl : A → A ⊎ B` and `inr : B → A ⊎ B` are embeddings, they must reflect isolated points.
```agda
isIsolatedFromInl : ∀ {a : A} → isIsolated (inl {B = B} a) → isIsolated a
isIsolatedFromInl = EmbeddingReflectIsolated inl Sum.isEmbedding-inl

isIsolatedFromInr : ∀ {b : B} → isIsolated (inr {A = A} b) → isIsolated b
isIsolatedFromInr = EmbeddingReflectIsolated inr Sum.isEmbedding-inr
```

In addition, both are _decidable_ embeddings, so they also create isolated points:
```agda
isIsolatedInl : ∀ {a : A} → isIsolated a → isIsolated (inl {B = B} a)
isIsolatedInl = DecEmbeddingCreateIsolated inl Sum.isEmbedding-inl Sum.decFiberInl

isIsolatedInr : ∀ {b : B} → isIsolated b → isIsolated (inr {A = A} b)
isIsolatedInr = DecEmbeddingCreateIsolated inr Sum.isEmbedding-inr Sum.decFiberInr

isIsolated≃isIsolatedInl : ∀ {a : A} → isIsolated a ≃ isIsolated (inl {B = B} a)
isIsolated≃isIsolatedInr : ∀ {b : B} → isIsolated b ≃ isIsolated (inr {A = A} b)
```

<!--
```agda
isIsolated≃isIsolatedInl {a} = propBiimpl→Equiv
  (isPropIsIsolated a)
  (isPropIsIsolated (inl a))
  isIsolatedInl
  isIsolatedFromInl

isIsolated≃isIsolatedInr {b} = propBiimpl→Equiv
  (isPropIsIsolated b)
  (isPropIsIsolated (inr b))
  isIsolatedInr
  isIsolatedFromInr
```
-->

From this, we can conclude that the isolated points of a sum are exactly a sum of isolated points.
```agda
IsolatedSumIso : Iso ((A ⊎ B) °) ((A °) ⊎ (B °))
IsolatedSumIso .Iso.fun (inl a , isolated-inl-a) = inl (a , isIsolatedFromInl isolated-inl-a)
IsolatedSumIso .Iso.fun (inr b , isolated-inr-b) = inr (b , isIsolatedFromInr isolated-inr-b)
IsolatedSumIso .Iso.inv (inl (a , isolated-a)) = inl a , isIsolatedInl isolated-a
IsolatedSumIso .Iso.inv (inr (b , isolated-b)) = inr b , isIsolatedInr isolated-b
IsolatedSumIso .Iso.rightInv (inl (a , _)) = cong inl $ Isolated≡ $ refl′ a
IsolatedSumIso .Iso.rightInv (inr (b , _)) = cong inr $ Isolated≡ $ refl′ b
IsolatedSumIso .Iso.leftInv (inl a , _) = Isolated≡ $ refl′ $ inl a
IsolatedSumIso .Iso.leftInv (inr b , _) = Isolated≡ $ refl′ $ inr b

IsolatedSumEquiv : (A ⊎ B) ° ≃ (A °) ⊎ (B °)
IsolatedSumEquiv = isoToEquiv IsolatedSumIso
```
