{-# OPTIONS --safe #-}
module Derivative.Isolated.Maybe where

open import Derivative.Prelude
open import Derivative.Isolated.Base

open import Derivative.Basics.Decidable as Dec
open import Derivative.Basics.Maybe
open import Derivative.Basics.Sum using (inlInj)
open import Derivative.Remove

private
  variable
    ℓ : Level
    A : Type ℓ

isIsolatedNothing : isIsolated {A = Maybe A} nothing
isIsolatedNothing (just a) = no nothing≢just
isIsolatedNothing nothing = yes refl

nothing° : (Maybe A) °
nothing° .fst = nothing
nothing° .snd = isIsolatedNothing

isIsolatedJust : ∀ {a : A} → isIsolated a → isIsolated (the (Maybe A) $ just a)
isIsolatedJust {a = a} a≟_ (just b) = Dec.map (cong just) (_∘ inlInj) (a≟ b)
isIsolatedJust {a = a} a≟_ nothing = no (nothing≢just ∘ sym)

just° : A ° → (Maybe A) °
just° (a , a≟_) .fst = just a
just° (a , a≟_) .snd = isIsolatedJust a≟_

module _ {ℓ} {A : Type ℓ} (a₀ : A) (a₀≟_ : isIsolated a₀) where
  unreplace : A → Maybe (A ∖ a₀)
  unreplace a with (a₀≟ a)
  ... | (yes _) = nothing
  ... | (no a₀≢a) = just (a , a₀≢a)

  replace-isolated-β-no : {a : A} → (a₀≢a : a₀ ≢ a) → unreplace a ≡ just (a , a₀≢a)
  replace-isolated-β-no {a} a₀≢a with (a₀≟ a)
  ... | (yes a₀≡a) = ex-falso $ a₀≢a a₀≡a
  ... | (no a₀≢a) = congS just (Remove≡ (refl′ a))

  unreplace-isolated-Iso : Iso A (Maybe (A ∖ a₀))
  unreplace-isolated-Iso .Iso.fun = unreplace
  unreplace-isolated-Iso .Iso.inv = replace a₀
  unreplace-isolated-Iso .Iso.rightInv (just (a , a₀≢a)) with a₀≟ a
  ... | (yes a₀≡a) = ex-falso (a₀≢a a₀≡a)
  ... | (no a₀≢a') = congS just $ ΣPathP (refl′ a , isProp¬ _ a₀≢a' a₀≢a)
  unreplace-isolated-Iso .Iso.rightInv nothing with a₀≟ a₀
  ... | (yes a₀≡a₀) = refl
  ... | (no a₀≢a₀) = ex-falso $ a₀≢a₀ refl
  unreplace-isolated-Iso .Iso.leftInv a with (a₀≟ a)
  ... | (yes a₀≡a) = a₀≡a
  ... | (no  a₀≢a) = refl′ a

  replace-isolated-equiv : Maybe (A ∖ a₀) ≃ A
  replace-isolated-equiv = isoToEquiv $ invIso $ unreplace-isolated-Iso

  unreplace-isolated-equiv : A ≃ (Maybe (A ∖ a₀))
  unreplace-isolated-equiv = isoToEquiv unreplace-isolated-Iso

isEquiv-replace→isIsolated : (a₀ : A)
  → isEquiv (replace a₀)
  → isIsolated a₀
isEquiv-replace→isIsolated {A} a₀ is-equiv = is-isolated-a₀ where
  equiv : A ≃ Maybe (A ∖ a₀)
  equiv = invEquiv (replace a₀ , is-equiv)

  is-isolated-a₀ : isIsolated a₀
  is-isolated-a₀ = isIsolatedRespectEquiv equiv nothing isIsolatedNothing

isIsolated≃isEquiv-replace : (a₀ : A)
  → isIsolated a₀ ≃ isEquiv (replace a₀)
isIsolated≃isEquiv-replace a₀ = propBiimpl→Equiv
  (isPropIsIsolated a₀) (isPropIsEquiv (replace a₀))
  (equivIsEquiv ∘ replace-isolated-equiv a₀)
  (isEquiv-replace→isIsolated a₀)
