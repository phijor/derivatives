{-# OPTIONS --safe #-}
module Derivative.Isolated.DependentGrafting where

open import Derivative.Prelude
open import Derivative.Basics.Decidable as Dec
open import Derivative.Isolated.Base
open import Derivative.Remove

private
  variable
    ℓ : Level
    A : Type ℓ
    B : A → Type ℓ

private
  pre-graft : (a₀ : A)
    → (f : (a : A ∖ a₀) → B (a .fst))
    → (b₀ : B a₀)
    → (a : A) → Dec (a₀ ≡ a) → B a
  pre-graft {B} a₀ f b₀ a (yes a₀≡a) = subst B a₀≡a b₀
  pre-graft {B} a₀ f b₀ a (no  a₀≢a) = f (a , a₀≢a)

  pre-graftᵝ : (a₀ : A)
    → (f : (a : A ∖ a₀) → B (a .fst))
    → (b₀ : B a₀)
    → ∀ a (b : B a)
    → (yes* : (a₀≡a : a₀ ≡ a) → PathP (λ i → B (a₀≡a i)) b₀ b)
    → (no*  : (a₀≢a : a₀ ≢ a) → f (a , a₀≢a) ≡ b)
    → (a₀≟a : Dec (a₀ ≡ a))
    → pre-graft a₀ f b₀ a a₀≟a ≡ b
  pre-graftᵝ {B} a₀ f b₀ a b yes* no* (yes a₀≡a) = fromPathP {A = λ i → B (a₀≡a i)} (yes* a₀≡a)
  pre-graftᵝ {B} a₀ f b₀ a b yes* no* (no  a₀≢a) = no* a₀≢a

  isPropLoop→PathP : (a : A)
    → isProp (a ≡ a)
    → (p : a ≡ a)
    → (b : B a)
    → PathP (λ i → B (p i)) b b
  isPropLoop→PathP {A} {B} a is-prop-loop p b = subst
    (λ (p : a ≡ a) → PathP (λ i → B (p i)) b b)
    (is-prop-loop refl p)
    (refl′ b)

graft : (a₀ : A °)
  → (f : (a : A ∖° a₀) → B (a .fst))
  → (b₀ : B (a₀ .fst))
  → (a : A) → B a
graft {B} (a₀ , a₀≟_) f b₀ a = pre-graft a₀ f b₀ a (a₀≟ a)

graftᵝ : (a₀ : A °)
  → (f : (a : A ∖° a₀) → B (a .fst))
  → (b₀ : B (a₀ .fst))
  → ∀ a (b : B a)
  → (yes* : (a₀≡a : a₀ .fst ≡ a) → PathP (λ i → B (a₀≡a i)) b₀ b)
  → (no* : (a₀≢a : a₀ .fst ≢ a) → f (a , a₀≢a) ≡ b)
  → graft a₀ f b₀ a ≡ b
graftᵝ (a₀ , a₀≟_) f b₀ a b yes* no* = pre-graftᵝ a₀ f b₀ a b yes* no* (a₀≟ a)

graft-Iso : (a₀ : A °) → Iso (((a : A ∖° a₀) → B (a .fst)) × B (a₀ .fst)) ((a : A) → B a)
graft-Iso a₀ .Iso.fun (f , b) = graft a₀ f b
graft-Iso a₀ .Iso.inv f .fst = f ∘ fst
graft-Iso a₀ .Iso.inv f .snd = f (a₀ .fst)
graft-Iso a₀ .Iso.rightInv f = funExt λ a → graftᵝ a₀ (f ∘ fst) (f (a₀ .fst)) a (f a)
  (λ a₀≡a → cong f a₀≡a)
  (λ _ → refl′ (f a))
graft-Iso {A} {B} a₀ .Iso.leftInv (f , b) = ΣPathP (funExt lemma₁ , lemma₂) where
  lemma₁ : (a : A ∖° a₀) → graft a₀ f b (a .fst) ≡ f a
  lemma₁ (a , a₀≢a) = graftᵝ a₀ f b a (f (a , a₀≢a))
    (λ a₀≡a → ex-falso $ a₀≢a a₀≡a)
    (λ a₀≢a' → cong (λ - → f (a , -)) (isProp≢ a₀≢a' a₀≢a))

  lemma₂ : graft a₀ f b (a₀ .fst) ≡ b
  lemma₂ = graftᵝ a₀ f b (a₀ .fst) b
    (λ a₀≡a₀ → isPropLoop→PathP {B = B} (a₀ .fst) (isIsolated→isPropPath (a₀ .fst) (a₀ .snd) _) a₀≡a₀ b)
    (λ a₀≢a₀ → ex-falso $ a₀≢a₀ refl)

graft-equiv : (a₀ : A °)
  → (((a : A ∖° a₀) → B (a .fst)) × B (a₀ .fst)) ≃ ((a : A) → B a)
graft-equiv = isoToEquiv ∘ graft-Iso
