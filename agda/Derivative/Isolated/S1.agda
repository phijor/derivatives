{-# OPTIONS --safe #-}
module Derivative.Isolated.S1 where

open import Derivative.Prelude
open import Derivative.Basics.S1 as S¹
open import Derivative.Basics.Decidable as Dec
open import Derivative.Basics.Embedding
open import Derivative.Isolated.Base

isIsolatedBase→isPropBaseLoop : isIsolated base → isProp (base ≡ base)
isIsolatedBase→isPropBaseLoop isolated-base p q = isEmbedding→Inj Dec.isEmbeddingYes p q yes-path where
  dec-base≡ : Dec (base ≡ base)
  dec-base≡ = isolated-base base

  is-prop-dec-base≡ : isProp (Dec (base ≡ base))
  is-prop-dec-base≡ = isIsolated→isPropDecPath base isolated-base base

  yes-path : yes p ≡ yes q
  yes-path = is-prop-dec-base≡ (yes p) (yes q)

¬isIsolated-base : ¬ isIsolated base
¬isIsolated-base isolated-base = refl≢loop (isIsolatedBase→isPropBaseLoop isolated-base refl loop)

isPerfectS¹ : isPerfect S¹
isPerfectS¹ = uncurry (S¹.elimProp (λ x → Dec.isProp¬ (isIsolated x)) ¬isIsolated-base)
