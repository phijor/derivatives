module Derivative.Derivative where

open import Derivative.Prelude
open import Derivative.Container
open import Derivative.Decidable
open import Derivative.Isolated
open import Derivative.Remove
open import Derivative.Maybe

open import Cubical.Data.Sigma.Base
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
∂[_] {F} {G} [ f ◁ u ] = ∂f where
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

module _ (F : Container ℓ ℓ) where
  open Container F renaming (Shape to S ; Pos to P)

  unit-shape : S → Σ[ s ∈ S × ⊤ ℓ ] (P (s .fst) ⊎ (⊤ ℓ)) °
  unit-shape s .fst = s , _
  unit-shape s .snd .fst = nothing
  unit-shape s .snd .snd = isIsolatedNothing

  unit-pos : (s : S) → Maybe (P s) ∖ nothing ≃ P s
  unit-pos s = removeNothingEquiv

  unit : Cart F (∂ (F ⊗Id))
  unit .shape = unit-shape
  unit .pos = unit-pos

module _ (G : Container ℓ ℓ) where
  open Container G renaming (Shape to T ; Pos to Q)
  counit-shape : (Σ[ t ∈ T ] (Q t) °) × (⊤ ℓ) → T
  counit-shape ((t , _ , _) , _) = t

  counit-pos : ∀ (t : T) (q : (Q t)) → isIsolated q → Q t ≃ ((Q t ∖ q) ⊎ ⊤ ℓ)
  counit-pos t q isolated-q = replace-isolated-equiv q isolated-q

  counit : Cart (∂ G ⊗Id) G
  counit .shape = counit-shape
  counit .pos ((t , q , isolated-q) , _) = counit-pos t q isolated-q

is-natural-counit : (F G : Container ℓ ℓ) (f : Cart F G) → [ ∂[ f ] ]⊗Id ⋆ counit G ≡ counit F ⋆ f
is-natural-counit F G f = Cart≡ refl $ funExt λ where
  ((s , p°) , _) → equivEq $ {! !}
