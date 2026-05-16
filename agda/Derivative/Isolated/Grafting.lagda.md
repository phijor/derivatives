<!--
```agda
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
```
-->

Given some `a₀ : A°`, we can define sections of any family `B : A → Type` by case analysis of `a₀ ≟ a`.
```agda
module _ {B : A → Type ℓ}
  ((a₀ , a₀≟_) : A °)
  (eq* : ∀ a → a₀ ≡ a → B a)
  (neq* : (a : A ∖ a₀) → B (a .fst))
  where
  elimIsolated : ∀ a → B a
  elimIsolated a = Dec.elim (eq* a) (λ neq → neq* (a , neq)) (a₀≟ a)

  elimIsolated-β-yes : ∀ a → (p : a₀ ≡ a) → elimIsolated a ≡ eq* a p
  elimIsolated-β-yes a p i = Dec.elim (eq* a) (λ neq → neq* (a , neq)) (isIsolated→isPropDecPath a₀ a₀≟_ a (a₀≟ a) (yes p) i)

  elimIsolated-β-refl : elimIsolated a₀ ≡ eq* a₀ refl
  elimIsolated-β-refl = elimIsolated-β-yes a₀ refl

  elimIsolated-β-no : ∀ a → (¬p : a₀ ≢ a) → elimIsolated a ≡ neq* (a , ¬p)
  elimIsolated-β-no a ¬p i = Dec.elim (eq* a) (λ neq → neq* (a , neq)) (isIsolated→isPropDecPath a₀ a₀≟_ a (a₀≟ a) (no ¬p) i)
```

This lets us define a recursion principle for a type `A` with some isolated point `a° : A°`:
To give a map `A → B`, it suffices to give `f : A ∖ a° → B`, and some point `b₀ : B`.
Note that this principle is not valid for arbitrary pointed types!
```agda
graft : (a° : A °) → ((A ∖° a° → B) × B) → (A → B)
graft a° (f , b₀) = elimIsolated a° (λ _ _ → b₀) f
```

This comes with the expected (propositional) computation rules, namely that
if `f* ≔ graft a° (f, b₀)`, then `f*(a°) = b₀` and `f*(a) = f(a)` for all `a ≠ a°`.
```agda
graft-β-yes : (a° : A °) (f : A ∖° a° → B) {b₀ : B} → graft a° (f , b₀) (a° .fst) ≡ b₀
graft-β-yes a° f {b₀} = elimIsolated-β-refl a° (λ _ _ → b₀) f

graft-β-no : (a° : A °) (f : A ∖° a° → B) {b₀ : B} (a : A ∖ a° .fst) → graft a° (f , b₀) (a .fst) ≡ f a
graft-β-no a° f {b₀} = uncurry $ elimIsolated-β-no a° (λ _ _ → b₀) f
```

There is a canonical map which decomposes a function `f : A → B` into two parts,
namely:

1. A map `A ∖ a° → B` by precomposing the restriction `A ∖ a° → A`
2. Some point `b₀ : B`, i.e. the image `f(a°) : B`.

```agda
ungraft : (a° : A °) → (A → B) → (((A ∖ a° .fst) → B) × B)
ungraft (a₀ , _) f .fst = f ∘ forget-remove a₀
ungraft (a₀ , _) f .snd = f a₀
```

We can show that `graft a°` is an equivalence with inverse `ungraft a°` by application of the the computation rules.
```agda
isEquiv-graft : (a° : A °) → isEquiv (graft {B = B} a°)
isEquiv-graft {A} {B} a°@(a₀ , a₀≟_) = isoToIsEquiv graft-iso module isEquivgraft where

  graft-iso : Iso (((A ∖ a₀) → B) × B) (A → B)
  graft-iso .Iso.fun = graft a°
  graft-iso .Iso.inv = ungraft a°
  graft-iso .Iso.rightInv f = funExt λ a → goal a (a₀≟ a) where
    goal : (a : A) → Dec (a₀ ≡ a) → graft a° (ungraft a° f) a ≡ f a
    goal a (yes p) = elimIsolated-β-yes a° (λ _ _ → f a₀) (f ∘ fst) a p ∙ cong f p
    goal a (no ¬p) = elimIsolated-β-no a° (λ _ _ → f a₀) (f ∘ fst) a ¬p
  graft-iso .Iso.leftInv (f° , b) = ΣPathP λ where
    .fst → funExt λ (a , a₀≢a) → elimIsolated-β-no a° (λ _ _ → b) f° a a₀≢a
    .snd → elimIsolated-β-refl a° (λ _ _ → b) f°

graftEquiv : (a° : A °) → ((A ∖ a° .fst → B) × B) ≃ (A → B)
graftEquiv a° .fst = graft a°
graftEquiv a° .snd = isEquiv-graft a°

ungraftEquiv : (a° : A °) → (A → B) ≃ ((A ∖ a° .fst → B) × B)
ungraftEquiv a° .fst = ungraft a°
ungraftEquiv a° .snd = isoToIsEquiv $ invIso $ isEquivgraft.graft-iso _ (a° .snd)
```

Consequently, every map `A → B` arises as an application of `graft a°`.
We can compute this directly.
```agda
graft-eval : (a° : A °) → (f : A → B) (b₀ : B)
  → (p : b₀ ≡ f (a° .fst))
  → graft a° (f ∘ forget-remove (a° .fst) , b₀) ≡ f
graft-eval a° f b₀ p using (a₀ , a₀≟_) ← a° = funExt λ a → eval-dec a (a₀≟ a) module graft-eval where
  eval-dec : ∀ a → Dec (a₀ ≡ a) → graft a° (f ∘ fst , b₀) a ≡ f a
  eval-dec a (yes a₀≡a) = elimIsolated-β-yes a° (λ _ _ → b₀) (f ∘ fst) a a₀≡a ∙∙ p ∙∙ cong f a₀≡a
  eval-dec a (no ¬a₀≡a) = graft-β-no a° (f ∘ fst) (a , ¬a₀≡a)
```

Over `a° : A°`, the above path is essentially the computation rule [`graft-β-yes`](#graft-β-yes).
There is a square of paths

                               p
               b₀ -------------------------> f a°
                ^                             ^
                |                             |
    graft-β-yes |                             | =
                |                             |
                |                             |
       graft a° (f, b₀) -------------------> f a°
                        graft-eval ≡$ a°


```agda
graft-eval-yes-filler : (a° : A °) → (f : A → B) (b₀ : B)
  → (p : b₀ ≡ f (a° .fst))
  → Square
    (graft-β-yes a° (f ∘ fst) {b₀ = b₀})
    (refl′ (f (a° .fst)))
    (graft-eval a° f b₀ p ≡$ a° .fst)
    p
graft-eval-yes-filler a° f b₀ p using (a₀ , a₀≟_) ← a° = λ i j → eval-dec-filler (a₀≟ a₀) (~ j) i module graft-eval-yes-filler where
  open graft-eval a° f b₀ p

  eval-dec-filler : (a₀≟a₀ : Dec (a₀ ≡ a₀)) → Square p (eval-dec a₀ a₀≟a₀) (sym $ graft-β-yes a° (f ∘ fst) {b₀}) (refl′ (f a₀))
  eval-dec-filler (yes a₀≡a₀) = goal
    where
      filler : Square p (eval-dec a₀ (yes a₀≡a₀)) _ (cong f a₀≡a₀)
      filler = doubleCompPath-filler (elimIsolated-β-yes a° (λ _ _ → b₀) (f ∘ fst) a₀ a₀≡a₀) p (cong f a₀≡a₀)

      trivial-loop : a₀≡a₀ ≡ refl
      trivial-loop = isIsolated→K a₀ a₀≟_ a₀≡a₀

      adjust₁ : cong f a₀≡a₀ ≡ refl
      adjust₁ i j = f (trivial-loop i j)

      adjust₂ : elimIsolated-β-yes a° (λ _ _ → b₀) (f ∘ fst) a₀ a₀≡a₀ ≡ graft-β-yes a° (f ∘ fst) {b₀}
      adjust₂ = cong (elimIsolated-β-yes a° _ (f ∘ fst) a₀) trivial-loop

      goal : Square p (eval-dec a₀ (yes a₀≡a₀)) (sym $ graft-β-yes a° (f ∘ fst)) (refl′ (f a₀))
      goal = subst2 (λ r s → Square p (eval-dec a₀ (yes a₀≡a₀)) (sym r) s) adjust₂ adjust₁ filler

  eval-dec-filler (no ¬a₀≡a₀) = ex-falso $ ¬a₀≡a₀ refl
```
