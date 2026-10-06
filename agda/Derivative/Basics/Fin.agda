{-# OPTIONS --safe #-}
module Derivative.Basics.Fin where

open import Derivative.Prelude
open import Derivative.Basics.Decidable using (Discrete ; isProp→Discrete)
open import Derivative.Basics.Unit
open import Derivative.Basics.Sum

Fin : ℕ → Type
Fin zero = 𝟘
Fin (suc n) = 𝟙 ⊎ Fin n

pattern fzero = inl •
pattern fsuc k = inr k

DiscreteFin : ∀ n → Discrete (Fin n)
DiscreteFin zero ()
DiscreteFin (suc n) = discrete⊎ (isProp→Discrete isProp-𝟙*) (DiscreteFin n)
