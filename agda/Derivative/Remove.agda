{-# OPTIONS --safe #-}
module Derivative.Remove where

open import Derivative.Prelude
open import Derivative.Basics.Decidable
open import Derivative.Basics.Equiv
open import Derivative.Basics.Path using (neqCongEquiv)
open import Derivative.Basics.Sigma
open import Derivative.Basics.Sum as Sum
open import Derivative.Isolated.Base

open import Cubical.Foundations.Equiv.Properties using (preCompEquiv ; equivAdjointEquiv ; congEquiv)
open import Cubical.Foundations.Path using (toPathP⁻ ; flipSquare)
open import Cubical.Foundations.Transport using (subst⁻ ; subst⁻-filler)
open import Cubical.Functions.Embedding using (_↪_ ; EmbeddingΣProp ; isEmbedding)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma
import      Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary using (isProp¬)

private
  variable
    ℓ : Level
    A B : Type ℓ

Remove : (A : Type ℓ) (a : A) → Type ℓ
Remove A a = Σ[ b ∈ A ] (a ≢ b)

_∖_ : (A : Type ℓ) (a : A) → Type ℓ
_∖_ = Remove

forget-remove : (a : A) → A ∖ a → A
forget-remove a = fst

forget-remove-embedding : (a : A) → (A ∖ a) ↪ A
forget-remove-embedding a = EmbeddingΣProp λ a → isProp≢

isEmbedding-forget-remove : (a : A) → isEmbedding (forget-remove a)
isEmbedding-forget-remove a = forget-remove-embedding a .snd

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

-- We can restrict removal of points from a type to isolated points.
-- We will show that removal is well-behaved exactly for isolated points.
-- ```agda
_∖°_ : (A : Type ℓ) (a : A °) → Type ℓ
A ∖° a = A ∖ forget-isolated a
-- ```

module _ {B : A → Type ℓ} {a₀ : A} {b₀ : B a₀}
  (a₀≟_ : isIsolated a₀)
  where
  private
    is-prop-a₀-loop : isProp (a₀ ≡ a₀)
    is-prop-a₀-loop = isIsolated→isPropPath a₀ a₀≟_ a₀

    Σ-remove' = Σ-remove {B = B} a₀ b₀ is-prop-a₀-loop

    Σ-remove-inv' : ∀ a → Dec (a₀ ≡ a) → (b : B a) → (a₀ , b₀) ≢ (a , b) → (Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀)
    Σ-remove-inv' a (yes a₀≡a) b neq = on-yes where
      b₀≢subst-b : b₀ ≢ subst⁻ B a₀≡a b
      b₀≢subst-b q = neq goal where
        b₀≡ᴰb : PathP (λ i → B (a₀≡a i)) b₀ b
        b₀≡ᴰb = toPathP⁻ q

        goal : (a₀ , b₀) ≡ (a , b)
        goal = ΣPathP (a₀≡a , b₀≡ᴰb)

      on-yes : (Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀)
      on-yes = inr (subst⁻ B a₀≡a b , b₀≢subst-b)
    Σ-remove-inv' a (no a₀≢a) b _ = inl ((a , a₀≢a) , b)

  Σ-remove-inv : (Σ A B ∖ (a₀ , b₀)) → (Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀)
  Σ-remove-inv ((a , b) , neq) = Σ-remove-inv' a (a₀≟ a) b neq

  Σ-remove-rinv : ∀ a → (a₀≟a : Dec (a₀ ≡ a)) → (b : B a) → (neq : (a₀ , b₀) ≢ (a , b))
    → Σ-remove a₀ b₀ is-prop-a₀-loop (Σ-remove-inv' a a₀≟a b neq) ≡ ((a , b) , neq)
  Σ-remove-rinv a (yes a₀≡a) b neq = Remove≡ goal where
    goal : (a₀ , subst⁻ B a₀≡a b) ≡ (a , b)
    goal = ΣPathP (a₀≡a , symP (subst⁻-filler B a₀≡a b))
  Σ-remove-rinv a (no a₀≢a) b neq = Remove≡ $ refl′ (a , b)

  Σ-remove-linv-left : ∀ a → (a₀≟a : Dec (a₀ ≡ a)) → (a₀≢a : a₀ ≢ a) → (b : B a)
    → (let x = inl ((a , a₀≢a) , b))
    → Σ-remove-inv' a a₀≟a b (Σ-remove' x .snd) ≡ x
  Σ-remove-linv-left a (yes a₀≡a) a₀≢a = ex-falso $ a₀≢a a₀≡a
  Σ-remove-linv-left a (no _) _ b = cong inl (ΣPathP (Remove≡ (refl′ a) , refl′ b))

  Σ-remove-linv-right : (a₀≟a₀ : Dec (a₀ ≡ a₀)) → (b : B a₀) → (b₀≢b : b₀ ≢ b)
    → (let x = inr (b , b₀≢b))
    → Σ-remove-inv' a₀ a₀≟a₀ b (Σ-remove' x .snd) ≡ x
  Σ-remove-linv-right (yes a₀≡a₀) b _ = cong inr $ Remove≡ goal where
    goal : subst⁻ B a₀≡a₀ b ≡ b
    goal = cong (λ p → subst⁻ B p b) (is-prop-a₀-loop a₀≡a₀ refl) ∙ substRefl {B = B} b
  Σ-remove-linv-right (no a₀≢a₀) = ex-falso $ a₀≢a₀ refl

  Σ-remove-Iso : Iso ((Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀)) (Σ A B ∖ (a₀ , b₀))
  Σ-remove-Iso .Iso.fun = Σ-remove'
  Σ-remove-Iso .Iso.inv = Σ-remove-inv
  Σ-remove-Iso .Iso.rightInv ((a , b) , neq) = Σ-remove-rinv a (a₀≟ a) b neq
  Σ-remove-Iso .Iso.leftInv (inl ((a , a₀≢a) , b)) = Σ-remove-linv-left a (a₀≟ a) a₀≢a b
  Σ-remove-Iso .Iso.leftInv (inr (b , b₀≢b)) = Σ-remove-linv-right (a₀≟ a₀) b b₀≢b

  isIsolatedFst→Σ-remove-equiv : ((Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀)) ≃ (Σ A B ∖ (a₀ , b₀))
  isIsolatedFst→Σ-remove-equiv = isoToEquiv Σ-remove-Iso

  isIsolatedFst→isEquiv-Σ-remove : isEquiv (Σ-remove {B = B} a₀ b₀ is-prop-a₀-loop)
  isIsolatedFst→isEquiv-Σ-remove = equivIsEquiv isIsolatedFst→Σ-remove-equiv


module Connected where
  open import Cubical.Homotopy.Connected
  import      Cubical.HITs.PropositionalTruncation as PT
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
