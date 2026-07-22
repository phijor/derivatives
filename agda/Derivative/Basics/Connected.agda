{-# OPTIONS --safe #-}
module Derivative.Basics.Connected where

open import Derivative.Prelude

import Cubical.HITs.PropositionalTruncation as PT

isConnected : ∀ {ℓ} (A : Type ℓ) → Type ℓ
isConnected A = (x y : A) → PT.∥ x ≡ y ∥₁
