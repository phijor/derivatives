{-# OPTIONS --safe #-}
module Derivative.Isolated.Grafting where

open import Derivative.Prelude
open import Derivative.Isolated.Base
open import Derivative.Basics.Decidable as Dec
open import Derivative.Remove

private
  variable
    ℓ : Level
    A B : Type ℓ

stitch : (a° : A °) → (((A ∖ a° .fst) → B) × B) → (A → B)
stitch a° (f , b₀) = elimIsolated a° (λ _ _ → b₀) f

stitch-β : (a° : A °) (f : (A ∖ a° .fst) → B) {b₀ : B} → stitch a° (f , b₀) (a° .fst) ≡ b₀
stitch-β a° f {b₀} = elimIsolated-β-refl a° (λ _ _ → b₀) f

stitch-β' : (a° : A °) (f : (A ∖ a° .fst) → B) {b₀ : B} (a : A ∖ a° .fst) → stitch a° (f , b₀) (a .fst) ≡ f a
stitch-β' a° f {b₀} = uncurry $ elimIsolated-β-no a° (λ _ _ → b₀) f

stitch-eval : (a° : A °) → (f : A → B) (b₀ : B)
  → (p : b₀ ≡ f (a° .fst))
  → stitch a° (f ∘ fst , b₀) ≡ f
stitch-eval a° f b₀ p using (a₀ , a₀≟_) ← a° = funExt λ a → eval-dec a (a₀≟ a) module stitch-eval where
  eval-dec : ∀ a → Dec (a₀ ≡ a) → stitch a° (f ∘ fst , b₀) a ≡ f a
  eval-dec a (yes a₀≡a) = elimIsolated-β-yes a° (λ _ _ → b₀) (f ∘ fst) a a₀≡a ∙∙ p ∙∙ cong f a₀≡a
  eval-dec a (no ¬a₀≡a) = stitch-β' a° (f ∘ fst) (a , ¬a₀≡a)

stitch-eval-yes-filler : (a° : A °) → (f : A → B) (b₀ : B)
  → (p : b₀ ≡ f (a° .fst))
  → Square (stitch-β a° (f ∘ fst) {b₀ = b₀}) (refl′ (f (a° .fst))) (stitch-eval a° f b₀ p ≡$ a° .fst) p
stitch-eval-yes-filler a° f b₀ p using (a₀ , a₀≟_) ← a° = λ i j → eval-dec-filler (a₀≟ a₀) (~ j) i module stitch-eval-yes-filler where
  open stitch-eval a° f b₀ p

  eval-dec-filler : (a₀≟a₀ : Dec (a₀ ≡ a₀)) → Square p (eval-dec a₀ a₀≟a₀) (sym $ stitch-β a° (f ∘ fst) {b₀}) (refl′ (f a₀))
  eval-dec-filler (yes a₀≡a₀) = goal
    where
      filler : Square p (eval-dec a₀ (yes a₀≡a₀)) _ (cong f a₀≡a₀)
      filler = doubleCompPath-filler (elimIsolated-β-yes a° (λ _ _ → b₀) (f ∘ fst) a₀ a₀≡a₀) p (cong f a₀≡a₀)

      adjust₁ : cong f a₀≡a₀ ≡ refl
      adjust₁ i j = f (isIsolated→K a° a₀≡a₀ i j)

      adjust₂ : elimIsolated-β-yes a° (λ _ _ → b₀) (f ∘ fst) a₀ a₀≡a₀ ≡ stitch-β a° (f ∘ fst) {b₀}
      adjust₂ = cong (elimIsolated-β-yes a° _ (f ∘ fst) a₀) (isIsolated→K a° a₀≡a₀)

      goal : Square p (eval-dec a₀ (yes a₀≡a₀)) (sym $ stitch-β a° (f ∘ fst)) (refl′ (f a₀))
      goal = subst2 (λ r s → Square p (eval-dec a₀ (yes a₀≡a₀)) (sym r) s) adjust₂ adjust₁ filler

  eval-dec-filler (no ¬a₀≡a₀) = ex-falso $ ¬a₀≡a₀ refl

unstitch : (a° : A °) → (A → B) → (((A ∖ a° .fst) → B) × B)
unstitch (a₀ , _) f .fst = f ∘ fst
unstitch (a₀ , _) f .snd = f a₀

isEquivStitch : (a° : A °) → isEquiv (stitch {B = B} a°)
isEquivStitch {A} {B} a°@(a₀ , a₀≟_) = isoToIsEquiv stich-iso module isEquivStitch where

  stich-iso : Iso (((A ∖ a₀) → B) × B) (A → B)
  stich-iso .Iso.fun = stitch a°
  stich-iso .Iso.inv = unstitch a°
  stich-iso .Iso.rightInv f = funExt λ a → goal a (a₀≟ a) where
    goal : (a : A) → Dec (a₀ ≡ a) → stitch a° (unstitch a° f) a ≡ f a
    goal a (yes p) = elimIsolated-β-yes a° (λ _ _ → f a₀) (f ∘ fst) a p ∙ cong f p
    goal a (no ¬p) = elimIsolated-β-no a° (λ _ _ → f a₀) (f ∘ fst) a ¬p
  stich-iso .Iso.leftInv (f° , b) = ΣPathP λ where
    .fst → funExt λ (a , a₀≢a) → elimIsolated-β-no a° (λ _ _ → b) f° a a₀≢a
    .snd → elimIsolated-β-refl a° (λ _ _ → b) f°

stitchEquiv : (a° : A °) → ((A ∖ a° .fst → B) × B) ≃ (A → B)
stitchEquiv a° .fst = stitch a°
stitchEquiv a° .snd = isEquivStitch a°

unstitchEquiv : (a° : A °) → (A → B) ≃ ((A ∖ a° .fst → B) × B)
unstitchEquiv a° .fst = unstitch a°
unstitchEquiv a° .snd = isoToIsEquiv $ invIso $ isEquivStitch.stich-iso _ (a° .snd)
