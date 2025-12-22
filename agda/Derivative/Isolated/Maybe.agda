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
  private
    replace? : (a : A) → Dec (a₀ ≡ a) → Maybe (A ∖ a₀)
    replace? a (yes _) = nothing
    replace? a (no a₀≢a) = just (a , a₀≢a)

  replace?-yes : replace? a₀ (a₀≟ a₀) ≡ nothing
  replace?-yes = cong (replace? a₀) p where
    p : (a₀≟ a₀) ≡ (yes refl)
    p = isIsolated→isPropDecPath a₀ a₀≟_ a₀ (a₀≟ a₀) (yes refl)

  replace?-no : (a : A ∖ a₀) → replace? (a .fst) (a₀≟ a .fst) ≡ just a
  replace?-no (a , a₀≢a) = cong (replace? a) $ isIsolated→isPropDecPath a₀ a₀≟_ a (a₀≟ a) (no a₀≢a)

  private
    -- Fun fact: For (a₀ ≢ a), this always compute correctly, even if we
    -- do not assume that a₀ is isolated (_≢_ is always a proposition).
    replace?-no' : (a : A ∖ a₀) → replace? (a .fst) (a₀≟ a .fst) ≡ just a
    replace?-no' (a , a₀≢a) = cong (replace? a) p where
      p' : (d : Dec (a₀ ≡ a)) → d ≡ no a₀≢a
      p' (yes a₀≡a) = ex-falso $ a₀≢a a₀≡a
      p' (no h) = cong no $ isProp≢ h a₀≢a

      p : (a₀≟ a) ≡ no a₀≢a
      p = p' (a₀≟ a)
    
  replace-isolated : A → Maybe (A ∖ a₀)
  replace-isolated a = replace? a (a₀≟ a)
    
  replace-isolated' : A → Maybe (A ∖ a₀)
  replace-isolated' a with (a₀≟ a)
  ... | (yes _) = nothing
  ... | (no a₀≢a) = just (a , a₀≢a)

  replace-isolated'-β-no : {a : A} → (a₀≢a : a₀ ≢ a) → replace-isolated' a ≡ just (a , a₀≢a)
  replace-isolated'-β-no {a} a₀≢a with (a₀≟ a)
  ... | (yes a₀≡a) = ex-falso $ a₀≢a a₀≡a
  ... | (no a₀≢a) = congS just (Remove≡ (refl′ a))

  replace-isolated'-Iso : Iso A (Maybe (A ∖ a₀))
  replace-isolated'-Iso .Iso.fun = replace-isolated'
  replace-isolated'-Iso .Iso.inv = unreplace-isolated a₀
  replace-isolated'-Iso .Iso.rightInv (just (a , a₀≢a)) with a₀≟ a
  ... | (yes a₀≡a) = ex-falso (a₀≢a a₀≡a)
  ... | (no a₀≢a') = congS just $ ΣPathP (refl′ a , isProp¬ _ a₀≢a' a₀≢a)
  replace-isolated'-Iso .Iso.rightInv nothing with a₀≟ a₀
  ... | (yes a₀≡a₀) = refl
  ... | (no a₀≢a₀) = ex-falso $ a₀≢a₀ refl
  replace-isolated'-Iso .Iso.leftInv a with (a₀≟ a)
  ... | (yes a₀≡a) = a₀≡a
  ... | (no  a₀≢a) = refl′ a

  replace-isolated-Iso : Iso A (Maybe (A ∖ a₀))
  replace-isolated-Iso .Iso.fun = replace-isolated
  replace-isolated-Iso .Iso.inv = unreplace-isolated a₀
  replace-isolated-Iso .Iso.rightInv (just a) = replace?-no a
  replace-isolated-Iso .Iso.rightInv nothing = replace?-yes
  replace-isolated-Iso .Iso.leftInv a with (a₀≟ a)
  ... | (yes a₀≡a) = a₀≡a
  ... | (no  a₀≢a) = refl′ a

  unreplace-isolated-equiv : Maybe (A ∖ a₀) ≃ A
  unreplace-isolated-equiv = isoToEquiv $ invIso $ replace-isolated-Iso

  replace-isolated-equiv : A ≃ (Maybe (A ∖ a₀))
  replace-isolated-equiv = isoToEquiv replace-isolated-Iso

  replace-isolated'-equiv : A ≃ (Maybe (A ∖ a₀))
  replace-isolated'-equiv = isoToEquiv replace-isolated'-Iso

isEquiv-unreplace-isolated→isIsolated : (a₀ : A)
  → isEquiv (unreplace-isolated a₀)
  → isIsolated a₀
isEquiv-unreplace-isolated→isIsolated {A} a₀ is-equiv = is-isolated-a₀ where
  equiv : A ≃ Maybe (A ∖ a₀)
  equiv = invEquiv (unreplace-isolated a₀ , is-equiv)

  is-isolated-a₀ : isIsolated a₀
  is-isolated-a₀ = isIsolatedRespectEquiv equiv nothing isIsolatedNothing

isIsolated≃isEquiv-unreplace-isolated : (a₀ : A)
  → isIsolated a₀ ≃ isEquiv (unreplace-isolated a₀)
isIsolated≃isEquiv-unreplace-isolated a₀ = propBiimpl→Equiv
  (isPropIsIsolated a₀) (isPropIsEquiv (unreplace-isolated a₀))
  (equivIsEquiv ∘ unreplace-isolated-equiv a₀)
  (isEquiv-unreplace-isolated→isIsolated a₀)
