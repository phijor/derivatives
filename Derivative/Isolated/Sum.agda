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

isIsolatedFromInl : ∀ {a : A} → isIsolated (inl {B = B} a) → isIsolated a
isIsolatedFromInl = EmbeddingReflectIsolated inl Sum.isEmbedding-inl

isIsolatedFromInr : ∀ {b : B} → isIsolated (inr {A = A} b) → isIsolated b
isIsolatedFromInr = EmbeddingReflectIsolated inr Sum.isEmbedding-inr

isIsolatedInl : ∀ {a : A} → isIsolated a → isIsolated (inl {B = B} a)
isIsolatedInl {a} isolated-a (inl a′) = Dec.decEquiv (cong inl , Sum.isEmbedding-inl a a′) (isolated-a a′)
isIsolatedInl {a} isolated-a (inr b) = no λ inl≡inr → Sum.⊎Path.encode _ _ inl≡inr .lower

isIsolatedInr : ∀ {b : B} → isIsolated b → isIsolated (inr {A = A} b)
isIsolatedInr {b} isolated-b (inl a) = no λ inr≡inl → Sum.⊎Path.encode _ _ inr≡inl .lower
isIsolatedInr {b} isolated-b (inr b′) = Dec.decEquiv (cong inr , Sum.isEmbedding-inr b b′) (isolated-b b′)

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

