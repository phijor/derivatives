module Derivative.Sum where

open import Derivative.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Sum public
open import Cubical.Functions.Embedding

private
  module Sum = Cubical.Data.Sum

private
  variable
    ℓ : Level
    A B : Type ℓ
    C D : A → Type ℓ

congInlEquiv : {x y : A} → (x ≡ y) ≃ (inl {B = B} x ≡ inl y)
congInlEquiv .fst = cong inl
congInlEquiv .snd = Sum.isEmbedding-inl _ _

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

⊎-right-Iso : ∀ {C : Type ℓ} → Iso B C → Iso (A ⊎ B) (A ⊎ C)
⊎-right-Iso iso .Iso.fun = ⊎-map-right (iso .Iso.fun)
⊎-right-Iso iso .Iso.inv = ⊎-map-right (iso .Iso.inv)
⊎-right-Iso iso .Iso.rightInv (inl a) = refl
⊎-right-Iso iso .Iso.rightInv (inr b) = cong inr (iso .Iso.rightInv b)
⊎-right-Iso iso .Iso.leftInv (inl a) = refl
⊎-right-Iso iso .Iso.leftInv (inr c) = cong inr (iso .Iso.leftInv c)

⊎-right-≃ : ∀ {C : Type ℓ} → (e : B ≃ C) → (A ⊎ B) ≃ (A ⊎ C)
⊎-right-≃ e = isoToEquiv (⊎-right-Iso (equivToIso e))

isEquiv→isEquiv-⊎-map-right : ∀ {C : Type ℓ} {f : B → C}
  → isEquiv f
  → isEquiv (⊎-map-right {A = A} f)
isEquiv→isEquiv-⊎-map-right {C} {f} is-equiv-f = equivIsEquiv (⊎-right-≃ (f , is-equiv-f))

⊎-right-≃' : ∀ {C : Type ℓ} → (e : B ≃ C) → (A ⊎ B) ≃ (A ⊎ C)
⊎-right-≃' e .fst = ⊎-map-right (equivFun e)
⊎-right-≃' {B} {A} {C} e .snd .equiv-proof = goal where
  goal : (y : A ⊎ C) → isContr (fiber (⊎-map-right {B = B} (equivFun e)) y)
  goal (inl a) = isContrRetract {B = singl a}
    (const (a , refl))
    (λ (a′ , p) → inl a′ , cong inl (sym p))
    (λ { (inl a′ , p) → ΣPathP (sym {!p!} , {! !}) ; (inr b , x) → {! !} })
    {! !}
  goal (inr c) = {! !}

isEquiv-⊎-map-right→isEquiv : ∀ {C : Type ℓ}
  → (f : B → C)
  → isEquiv (⊎-map-right {A = A} f)
  → isEquiv f
isEquiv-⊎-map-right→isEquiv {A} {C} f is-equiv-map .equiv-proof = goal where

  fiber-equiv : (c : C) → fiber (⊎-map-right {A = A} f) (inr c) ≃ fiber f c
  fiber-equiv c = {! !}

  goal : (c : C) → isContr (fiber f c)
  goal c = isOfHLevelRespectEquiv 0 {! !} (is-equiv-map .equiv-proof (inr c))

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
⊎-empty-right ¬B .fst = inl
⊎-empty-right ¬B .snd .equiv-proof (inl a) = isOfHLevelRespectEquiv 0 fiber-equiv (isContrSingl a) where
  fiber-equiv : singl a ≃ fiber inl (inl a)
  fiber-equiv = Σ-cong-equiv-snd λ a′ → symEquiv ∙ₑ congInlEquiv
⊎-empty-right ¬B .snd .equiv-proof (inr b) = ex-falso (¬B b)

⊎-fiber-≃ : {C : Type ℓ} {f : A ⊎ B → C} → ∀ y → fiber f y ≃ (fiber (f ∘ inl) y) ⊎ (fiber (f ∘ inr) y)
⊎-fiber-≃ y = Σ-⊎-fst-≃
