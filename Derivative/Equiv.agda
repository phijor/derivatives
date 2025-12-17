module Derivative.Equiv where

open import Derivative.Prelude

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
