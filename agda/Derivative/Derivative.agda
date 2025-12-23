{-# OPTIONS --allow-unsolved-metas #-}
module Derivative.Derivative where

open import Derivative.Prelude
open import Derivative.Container
open import Derivative.Basics.Decidable as Dec
open import Derivative.Basics.Maybe
open import Derivative.Isolated
open import Derivative.Remove

open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Nat.Base using (_+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sum.Base as Sum using (_⊎_ ; inl ; inr)

private
  variable
    ℓ ℓS ℓP : Level

open Container
open Cart

∂ : (F : Container ℓS ℓP) → Container (ℓ-max ℓS ℓP) ℓP
∂ F .Shape = Σ[ s ∈ F .Shape ] (F .Pos s) °
∂ F .Pos (s , p , _) = (F .Pos s) ∖ p

∂[_] : {F G : Container ℓS ℓP} → Cart F G → Cart (∂ F) (∂ G)
∂[_] {F} {G} [ f ◁ u ] = ∂f module ∂[-] where
  ∂-shape : (Σ[ s ∈ F .Shape ] F .Pos s °) → (Σ[ t ∈ G .Shape ] G .Pos t °)
  ∂-shape (s , _) .fst = f s
  ∂-shape (s , (p , isolated-p)) .snd .fst = invEq (u s) p
  ∂-shape (s , (p , isolated-p)) .snd .snd = isIsolatedRespectEquiv (u s) p isolated-p

  ∂-pos : (s : F .Shape) (p : F .Pos s °) → (G .Pos (f s) ∖ invEq (u s) (p .fst)) ≃ (F .Pos s ∖ (p .fst))
  ∂-pos s p = RemoveRespectEquiv (p .fst) (u s)

  ∂f : Cart (∂ F) (∂ G)
  ∂f .shape = ∂-shape
  ∂f .pos = uncurry ∂-pos
  {-# INLINE ∂f #-}

isOfHLevelDerivative : {F : Container ℓS ℓP} {n k : HLevel}
  → isOfHLevel (2 + n) (F .Shape)
  → (∀ s → isOfHLevel (1 + k) (F .Pos s))
  → isOfHLevel (2 + n) (∂ F .Shape) × (∀ s → isOfHLevel (1 + k) (∂ F .Pos s))
isOfHLevelDerivative {F} {n} {k} is-trunc-shape is-trunc-pos = is-trunc-∂-shape , λ (s , p , _) → is-trunc-∂-pos s p where
  open Container F renaming (Shape to S ; Pos to P)

  is-trunc-∂-shape : isOfHLevel (2 + n) (Σ[ s ∈ S ] (P s) °)
  is-trunc-∂-shape = isOfHLevelΣ (2 + n) is-trunc-shape λ s → isOfHLevelPlus' 2 isSetIsolated

  is-trunc-∂-pos : ∀ s (p : P s) → isOfHLevel (1 + k) (P s ∖ p)
  is-trunc-∂-pos s p = isOfHLevelRemove k (is-trunc-pos s)

isTruncatedDerivative : {F : Container ℓS ℓP} (n k : HLevel)
  → isTruncatedContainer (2 + n) (1 + k) F
  → isTruncatedContainer (2 + n) (1 + k) (∂ F)
isTruncatedDerivative n k = uncurry isOfHLevelDerivative
