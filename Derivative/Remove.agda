{-# OPTIONS --safe #-}
module Derivative.Remove where

open import Derivative.Prelude
open import Derivative.Decidable
open import Derivative.Sum as Sum

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

remove-left-Iso : ∀ {a : A} → Iso ((A ∖ a) ⊎ B) ((A ⊎ B) ∖ (inl a))
remove-left-Iso .Iso.fun (inl (a′ , neq)) = inl a′ , neq ∘ Sum.inlInj
remove-left-Iso .Iso.fun (inr b) = inr b , Sum.inr≢inl ∘ sym
remove-left-Iso .Iso.inv (inl a′ , neq) = inl (a′ , neq ∘ cong inl)
remove-left-Iso .Iso.inv (inr b , _) = inr b
remove-left-Iso .Iso.rightInv (inl a′ , _) = Remove≡ refl
remove-left-Iso .Iso.rightInv (inr b , _) = Remove≡ refl
remove-left-Iso .Iso.leftInv (inl (a′ , neq)) = cong inl (Remove≡ refl)
remove-left-Iso .Iso.leftInv (inr b) = refl

remove-left-equiv : ∀ {a : A} → ((A ∖ a) ⊎ B) ≃ ((A ⊎ B) ∖ (inl a))
remove-left-equiv = isoToEquiv remove-left-Iso

remove-right-Iso : ∀ {b : B} → Iso (A ⊎ (B ∖ b)) ((A ⊎ B) ∖ (inr b))
remove-right-Iso .Iso.fun (inl a) = inl a , Sum.inr≢inl
remove-right-Iso .Iso.fun (inr (b′ , b′≢b)) = inr b′ , b′≢b ∘ Sum.inrInj
remove-right-Iso .Iso.inv (inl a , _) = inl a
remove-right-Iso .Iso.inv (inr b′ , inr-b′≢inr-b) = inr (b′ , inr-b′≢inr-b ∘ cong inr)
remove-right-Iso .Iso.rightInv (inl a , _) = Remove≡ (refl′ (inl a))
remove-right-Iso .Iso.rightInv (inr b′ , _) = Remove≡ (refl′ (inr b′))
remove-right-Iso .Iso.leftInv (inl a) = refl′ (inl a)
remove-right-Iso .Iso.leftInv (inr (b′ , _)) = cong inr $ Remove≡ $ refl′ b′

remove-right-equiv : ∀ {b : B} → (A ⊎ (B ∖ b)) ≃ ((A ⊎ B) ∖ (inr b))
remove-right-equiv = isoToEquiv remove-right-Iso


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

module Connected where
  open import Cubical.Homotopy.Connected
  open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
  import      Cubical.HITs.Truncation as Tr

  isConnectedSuc→inh : ∀ k → isConnected (suc k) A → ∥ A ∥₁
  isConnectedSuc→inh k (trunc-center , _) = Tr.rec (isProp→isOfHLevelSuc k PT.isPropPropTrunc) PT.∣_∣₁ trunc-center

  isConnectedSuc→inhPath : ∀ k → isConnected (2 + k) A → (a b : A) → ∥ a ≡ b ∥₁
  isConnectedSuc→inhPath k conn-A a b = isConnectedSuc→inh k $ isConnectedPath (suc k) conn-A a b

  isConnected→isEmptyRemove : isConnected 2 A → ∀ a₀ → ¬ (A ∖ a₀)
  isConnected→isEmptyRemove {A} 2-conn-A a₀ (a , a₀≢a) = contradiction where
    1-conn-path : isConnected 1 (a₀ ≡ a)
    1-conn-path = isConnectedPath 1 2-conn-A _ _

    mere-path : Tr.∥ a₀ ≡ a ∥ 1
    mere-path = 1-conn-path .fst

    contradiction : Empty.⊥
    contradiction = Tr.rec {n = 1} Empty.isProp⊥ a₀≢a mere-path

  isConnected+2→isEmptyRemove : ∀ k → isConnected (k + 2) A → ∀ a₀ → ¬ (A ∖ a₀)
  isConnected+2→isEmptyRemove k = isConnected→isEmptyRemove ∘ isConnectedSubtr 2 k
