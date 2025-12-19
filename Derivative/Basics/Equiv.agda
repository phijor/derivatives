{-# OPTIONS --safe #-}
module Derivative.Basics.Equiv where

open import Derivative.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence using (EquivJ)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level
    A B C : Type ℓ

preCompEquivFiberEquiv : (e : A ≃ B) (f : B → C) → ∀ c → fiber (equivFun e ⨟ f) c ≃ fiber f c
preCompEquivFiberEquiv {A} {B} {C} e f c =
  Σ[ a ∈ A ] f (equivFun e a) ≡ c
    ≃⟨ ⨟-fiber-equiv (equivFun e) f c ⟩
  Σ[ (b , _) ∈ fiber f c ] fiber (equivFun e) b
    ≃⟨ Σ-contractSnd (λ (b , _) → equivIsEquiv e .equiv-proof b) ⟩
  Σ[ b ∈ B ] f b ≡ c
    ≃∎

equivAdjointEquivExtCodomain : (e : A ≃ B) (f : C → A) (g : C → B)
  → (f ≡ invEq e ∘ g) ≃ (equivFun e ∘ f ≡ g)
equivAdjointEquivExtCodomain {C} e f g = invEquiv funExtEquiv ∙ₑ equivΠCod lemma ∙ₑ funExtEquiv where
  lemma : ∀ (c : C) → (f c ≡ invEq e (g c)) ≃ (equivFun e (f c) ≡ g c)
  lemma c = equivAdjointEquiv e

equivAdjointEquivExtDomain : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : Type ℓ'}
  → (e : A ≃ B) (f : B → C) (g : A → C)
  → (g ∘ invEq e ≡ f) ≃ (g ≡ f ∘ equivFun e)
equivAdjointEquivExtDomain {B} {C} =
  EquivJ
    (λ A e → (f : B → C) (g : A → C) → (g ∘ invEq e ≡ f) ≃ (g ≡ f ∘ equivFun e))
    (λ f g → idEquiv (g ≡ f))

lineEquiv : ∀ {A B : I → Type ℓ} (f : (i : I) → A i → B i)
  → (is-equiv₀ : isEquiv (f i0))
  → (is-equiv₁ : isEquiv (f i1))
  → ∀ φ → A φ ≃ B φ
lineEquiv f is-equiv₀ is-equiv₁ φ = λ where
  .fst → f φ
  .snd → isProp→PathP (λ i → isPropIsEquiv (f i)) is-equiv₀ is-equiv₁ φ

secEquiv : (e : A ≃ B) → ∀ (φ : I) → B ≃ B
secEquiv {B} e = lineEquiv (λ φ b → secEq e b φ) (equivIsEquiv (invEquiv e ∙ₑ e)) (idIsEquiv B)

retEquiv : (e : A ≃ B) → ∀ (φ : I) → A ≃ A
retEquiv {A} e = lineEquiv (λ φ a → retEq e a φ) (equivIsEquiv (e ∙ₑ invEquiv e)) (idIsEquiv A)
