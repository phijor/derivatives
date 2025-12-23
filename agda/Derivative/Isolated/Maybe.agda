{-# OPTIONS --safe #-}
module Derivative.Isolated.Maybe where

open import Derivative.Prelude
open import Derivative.Isolated.Base
open import Derivative.Isolated.Sum

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

isIsolatedFromJust : ∀ {a : A} → isIsolated (the (Maybe A) $ just a) → isIsolated a
isIsolatedFromJust = isIsolatedFromInl

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

remove-just : (a₀ : A) → Maybe A ∖ just a₀ → A
remove-just a₀ (just a , _) = a
remove-just a₀ (nothing , _) = a₀

removeJustIso : (a₀ : A) → isIsolated a₀ → Iso (Maybe A ∖ just a₀) A
removeJustIso a₀ a₀≟_ .Iso.fun = remove-just a₀
removeJustIso {A} a₀ a₀≟_ .Iso.inv = λ a → g a (a₀≟ a) module removeJustIso-inv where
  g : (a : A) → Dec (a₀ ≡ a) → Maybe A ∖ just a₀
  g a (yes a₀≡a) = nothing , nothing≢just ∘ sym
  g a (no ¬a₀≡a) = just a , ¬a₀≡a ∘ inlInj
removeJustIso a₀ a₀≟_ .Iso.rightInv a = rinv a (a₀≟ a) where
  open removeJustIso-inv a₀ a₀≟_
  rinv : ∀ a → (a₀≟a : Dec (a₀ ≡ a)) → remove-just a₀ (g a a₀≟a) ≡ a
  rinv a (yes a₀≡a) = a₀≡a
  rinv a (no ¬a₀≡a) = refl′ a
removeJustIso a₀ a₀≟_ .Iso.leftInv (just a , just-a₀≢just-a) = linv a just-a₀≢just-a (a₀≟ a) where
  open removeJustIso-inv a₀ a₀≟_

  linv : ∀ a → (h : just a₀ ≢ just a) → (a₀≟a : Dec (a₀ ≡ a)) → g a a₀≟a ≡ (just a , h)
  linv a h (yes a₀≡a) = ≢-rec (cong just a₀≡a) h
  linv a _ (no     _) = Remove≡ $ refl′ $ just a
removeJustIso a₀ a₀≟_ .Iso.leftInv (nothing , just-a₀≢nothing) = linv (a₀≟ a₀) where
  open removeJustIso-inv a₀ a₀≟_

  linv : (a₀≟a₀ : Dec (a₀ ≡ a₀)) → g a₀ a₀≟a₀ ≡ (nothing , just-a₀≢nothing)
  linv (yes a₀≡a₀) = Remove≡ $ refl′ $ nothing
  linv (no ¬a₀≡a₀) = ≢-rec refl ¬a₀≡a₀

removeJustEquiv : (a₀ : A) → isIsolated a₀ → (Maybe A ∖ just a₀) ≃ A
removeJustEquiv a₀ a₀≟_ = isoToEquiv $ removeJustIso a₀ a₀≟_
