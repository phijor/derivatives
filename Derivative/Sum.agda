module Derivative.Sum where

open import Derivative.Prelude

open import Cubical.Data.Sum public
open import Cubical.Functions.Embedding

module Sum = Cubical.Data.Sum

private
  variable
    ℓ : Level
    A B : Type ℓ
    C D : A → Type ℓ

inlInj : ∀ {x y : A} → inl {B = B} x ≡ inl y → x ≡ y
inlInj = isEmbedding→Inj Sum.isEmbedding-inl _ _

inrInj : ∀ {x y : B} → inr {A = A} x ≡ inr y → x ≡ y
inrInj = isEmbedding→Inj Sum.isEmbedding-inr _ _

inr≢inl : ∀ {x : A} {y : B} → inr x ≢ inl y
inr≢inl p = Sum.⊎Path.encode _ _ p .lower

Σ-⊎-fst-≃ : {E : A ⊎ B → Type ℓ} → (Σ (A ⊎ B) E) ≃ (Σ A (E ∘ inl) ⊎ Σ B (E ∘ inr))
Σ-⊎-fst-≃ = Sum.Σ⊎≃

Σ-⊎-snd-Iso : Iso (Σ[ a ∈ A ] C a ⊎ D a) (Σ A C ⊎ Σ A D)
Σ-⊎-snd-Iso .Iso.fun = uncurry λ a → Sum.rec (λ b → inl (a , b)) (λ c → inr (a , c))
Σ-⊎-snd-Iso .Iso.inv = Sum.rec (λ (a , b) → a , inl b) (λ (a , c) → a , inr c)
Σ-⊎-snd-Iso .Iso.rightInv = Sum.elim (λ _ → refl) (λ _ → refl)
Σ-⊎-snd-Iso .Iso.leftInv = uncurry λ a → Sum.elim (λ b → refl) (λ c → refl)

Σ-⊎-snd-≃ : (Σ[ a ∈ A ] C a ⊎ D a) ≃ (Σ A C ⊎ Σ A D)
Σ-⊎-snd-≃ = isoToEquiv Σ-⊎-snd-Iso

⊎-map-left : ∀ {C : Type ℓ} → (f : A → B) → (A ⊎ C) → (B ⊎ C)
⊎-map-left f (inl a) = inl (f a)
⊎-map-left f (inr b) = inr b

⊎-left-Iso : ∀ {C : Type ℓ} → Iso A B → Iso (A ⊎ C) (B ⊎ C)
⊎-left-Iso iso .Iso.fun = ⊎-map-left (iso .Iso.fun)
⊎-left-Iso iso .Iso.inv = ⊎-map-left (iso .Iso.inv)
⊎-left-Iso iso .Iso.rightInv (inl a) = cong inl (iso .Iso.rightInv a)
⊎-left-Iso iso .Iso.rightInv (inr c) = refl
⊎-left-Iso iso .Iso.leftInv (inl b) = cong inl (iso .Iso.leftInv b)
⊎-left-Iso iso .Iso.leftInv (inr c) = refl

⊎-left-≃ : ∀ {C : Type ℓ} → (e : A ≃ B) → (A ⊎ C) ≃ (B ⊎ C)
⊎-left-≃ e = isoToEquiv (⊎-left-Iso (equivToIso e))

⊎-map-right : ∀ {C : Type ℓ} → (f : B → C) → (A ⊎ B) → (A ⊎ C)
⊎-map-right f (inl a) = inl a
⊎-map-right f (inr b) = inr (f b)

⊎-empty-left-Iso : (¬ A) → Iso B (A ⊎ B)
⊎-empty-left-Iso ¬A .Iso.fun = inr
⊎-empty-left-Iso ¬A .Iso.inv (inl a) = ex-falso $ ¬A a
⊎-empty-left-Iso ¬A .Iso.inv (inr b) = b
⊎-empty-left-Iso ¬A .Iso.rightInv (inl a) = ex-falso $ ¬A a
⊎-empty-left-Iso ¬A .Iso.rightInv (inr b) = refl
⊎-empty-left-Iso ¬A .Iso.leftInv b = refl

⊎-empty-left : (¬ A) → B ≃ (A ⊎ B)
⊎-empty-left = isoToEquiv ∘ ⊎-empty-left-Iso

⊎-empty-right : (¬ B) → A ≃ (A ⊎ B)
⊎-empty-right = {! !}
