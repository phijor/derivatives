{-# OPTIONS --safe #-}
module Derivative.Basics.S1 where

open import Derivative.Prelude
import Derivative.Basics.Connected as Connected

open import Cubical.HITs.S1.Base public
import Cubical.HITs.S1.Properties as S1
import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Int using (0≢1-ℤ)

elimProp : ∀ {ℓP} {P : S¹ → Type ℓP}
  → (∀ x → isProp (P x))
  → P base
  → ∀ x → P x
elimProp {P = P} is-prop-P base* base = base*
elimProp {P = P} is-prop-P base* (loop i) = isProp→PathP (λ i → is-prop-P (loop i)) base* base* i

refl≢loop : refl ≢ loop
refl≢loop refl≡loop = 0≢1-ℤ (cong winding refl≡loop)

isConnected : Connected.isConnected S¹
isConnected = elimProp (λ x → isPropΠ λ y → PT.isPropPropTrunc) S1.isConnectedS¹
