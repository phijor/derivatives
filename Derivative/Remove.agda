module Derivative.Remove where

open import Derivative.Prelude
open import Derivative.Decidable

open import Cubical.Foundations.Equiv.Properties using (preCompEquiv ; equivAdjointEquiv)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (isProp¬)

private
  variable
    ℓ : Level
    A B : Type ℓ

Remove : (A : Type ℓ) (a : A) → Type ℓ
Remove A a = Σ[ b ∈ A ] (a ≢ b)

_∖_ : (A : Type ℓ) (a : A) → Type ℓ
_∖_ = Remove

Remove≡ : {a : A} {x y : A ∖ a} → x .fst ≡ y .fst → x ≡ y
Remove≡ {a} = Σ≡Prop λ a′ → isProp¬ (a ≡ a′)

RemoveRespectEquiv : (b : B) (e : A ≃ B) → (A ∖ invEq e b) ≃ B ∖ b
RemoveRespectEquiv b e = Σ-cong-equiv e neq-equiv module RemoveRespectEquiv where
  opaque
    neq-equiv : ∀ a → (invEq e b ≢ a) ≃ (b ≢ equivFun e a)
    neq-equiv a = preCompEquiv $ symEquiv ∙ₑ invEquiv (equivAdjointEquiv e) ∙ₑ symEquiv
