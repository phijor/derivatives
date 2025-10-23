module Derivative.Remove where

open import Derivative.Prelude
open import Derivative.Decidable
open import Derivative.Sum

open import Cubical.Foundations.Equiv.Properties using (preCompEquiv ; equivAdjointEquiv ; congEquiv)
open import Cubical.Functions.Embedding using (_↪_ ; EmbeddingΣProp)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Unit as Unit using (Unit*)
open import Cubical.Data.Empty as Empty using (⊥*)
open import Cubical.Relation.Nullary using (isProp¬)

private
  variable
    ℓ : Level
    A B : Type ℓ

Remove : (A : Type ℓ) (a : A) → Type ℓ
Remove A a = Σ[ b ∈ A ] (a ≢ b)

_∖_ : (A : Type ℓ) (a : A) → Type ℓ
_∖_ = Remove


remove-embedding : (a : A) → (A ∖ a) ↪ A
remove-embedding a = EmbeddingΣProp λ a → isProp≢

Remove≡ : {a : A} {x y : A ∖ a} → x .fst ≡ y .fst → x ≡ y
Remove≡ {a} = Σ≡Prop λ a′ → isProp¬ (a ≡ a′)

isOfHLevelRemove : ∀ {a} → (n : HLevel) → isOfHLevel (suc n) A → isOfHLevel (suc n) (A ∖ a)
isOfHLevelRemove n is-trunc-A = isOfHLevelSucΣSndProp n is-trunc-A λ a′ → isProp≢

RemoveRespectEquiv : (b : B) (e : A ≃ B) → (A ∖ invEq e b) ≃ B ∖ b
RemoveRespectEquiv b e = Σ-cong-equiv e neq-equiv module RemoveRespectEquiv where
  opaque
    neq-equiv : ∀ a → (invEq e b ≢ a) ≃ (b ≢ equivFun e a)
    neq-equiv a = preCompEquiv $ symEquiv ∙ₑ invEquiv (equivAdjointEquiv e) ∙ₑ symEquiv

RemoveRespectEquiv' : (a : A) (e : A ≃ B) → (A ∖ a) ≃ B ∖ equivFun e a
RemoveRespectEquiv' a e = Σ-cong-equiv e λ a → neqCongEquiv (congEquiv e)

isProp→isEmptyRemove : isProp A → ∀ a₀ → ¬ (A ∖ a₀)
isProp→isEmptyRemove is-prop a₀ (a , a₀≢a) = a₀≢a (is-prop a₀ a)

isContr→isEmptyRemove : isContr A → ∀ a₀ → ¬ (A ∖ a₀)
isContr→isEmptyRemove = isProp→isEmptyRemove ∘ isContr→isProp

RemoveUnit : ¬ ((Unit* {ℓ}) ∖ tt*)
RemoveUnit = isContr→isEmptyRemove Unit.isContrUnit* _

RemoveUnitEquiv : ∀ {ℓ′} → ((Unit* {ℓ}) ∖ tt*) ≃ ⊥* {ℓ′}
RemoveUnitEquiv = Empty.uninhabEquiv RemoveUnit lower

module _ {B : A → Type ℓ} (a₀ : A) (b₀ : B a₀) (is-prop-a₀-loop : isProp (a₀ ≡ a₀)) where
  Σ-remove : (Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀) → (Σ A B ∖ (a₀ , b₀))
  Σ-remove (inl ((a , a₀≢a) , b)) = (a , b) , the ((a₀ , b₀) ≢ (a , b)) λ a₀b₀≡ab → a₀≢a (cong fst a₀b₀≡ab)
  Σ-remove (inr (b , b₀≢b)) = (a₀ , b) , goal where
    module _ (a₀b₀≡a₀b : (a₀ , b₀) ≡ (a₀ , b)) where
      a₀≡a₀ : a₀ ≡ a₀
      a₀≡a₀ = cong fst a₀b₀≡a₀b

      b₀≡ᴰb : PathP (λ i → B (a₀≡a₀ i)) b₀ b
      b₀≡ᴰb = cong snd a₀b₀≡a₀b

      b₀≡b : b₀ ≡ b
      b₀≡b = subst (λ (p : a₀ ≡ a₀) → PathP (λ i → B (p i)) b₀ b) (is-prop-a₀-loop a₀≡a₀ refl) b₀≡ᴰb

      goal : Empty.⊥
      goal = b₀≢b b₀≡b
      {-# INLINE goal #-}
