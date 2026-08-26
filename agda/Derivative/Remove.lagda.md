## Removing points from a type

<!--
```agda
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
```
-->

The type \( A \) with some \( a : A \) removed, written \( A ∖ a \).
```agda
Remove : (A : Type ℓ) (a : A) → Type ℓ
Remove A a = Σ[ b ∈ A ] (a ≢ b)

_∖_ : (A : Type ℓ) (a : A) → Type ℓ
_∖_ = Remove
```

Inequality \( a \neq b \) is a proposition.
The forgetful map \( A ∖ a → A \) is therefore a subtype embedding.
```agda
forget-remove : (a : A) → A ∖ a → A
forget-remove a = fst

forget-remove-embedding : (a : A) → (A ∖ a) ↪ A
forget-remove-embedding a = EmbeddingΣProp λ a → isProp≢

isEmbedding-forget-remove : (a : A) → isEmbedding (forget-remove a)
isEmbedding-forget-remove a = forget-remove-embedding a .snd
```

For the same reason paths in \( A ∖ a \) are equivalent to those in \( A \).
```agda
Remove≡ : {a : A} {x y : A ∖ a} → x .fst ≡ y .fst → x ≡ y
Remove≡ {a} = Σ≡Prop λ a′ → isProp¬ (a ≡ a′)

isOfHLevelRemove : ∀ {a} → (n : HLevel) → isOfHLevel (suc n) A → isOfHLevel (suc n) (A ∖ a)
isOfHLevelRemove n is-trunc-A = isOfHLevelSucΣSndProp n is-trunc-A λ a′ → isProp≢
```

Equivalences respect isolated points.
```agda
RemoveRespectEquiv : (a : A) (e : A ≃ B) → (A ∖ a) ≃ B ∖ equivFun e a
RemoveRespectEquiv a e = Σ-cong-equiv e λ a → neqCongEquiv (congEquiv e)

RemoveRespectInvEquiv : (b : B) (e : A ≃ B) → (A ∖ invEq e b) ≃ B ∖ b
RemoveRespectInvEquiv b e = Σ-cong-equiv e neq-equiv module RemoveRespectInvEquiv where
  opaque
    neq-equiv : ∀ a → (invEq e b ≢ a) ≃ (b ≢ equivFun e a)
    neq-equiv a = preCompEquiv $ symEquiv ∙ₑ invEquiv (equivAdjointEquiv e) ∙ₑ symEquiv
```

We can restrict removal of points from a type to isolated points.
We will show that removal is well-behaved exactly for isolated points.
```agda
_∖°_ : (A : Type ℓ) (a : A °) → Type ℓ
A ∖° a = A ∖ forget-isolated a
```

If \( A \) is a proposition then it has at most one point.
If we remove that point, the resulting type is empty.
```agda
isProp→isEmptyRemove : isProp A → ∀ a₀ → ¬ (A ∖ a₀)
isProp→isEmptyRemove is-prop a₀ (a , a₀≢a) = a₀≢a (is-prop a₀ a)
```

The same applies to types that are contractible, i.e. homotopically a point:
```agda
isContr→isEmptyRemove : isContr A → ∀ a₀ → ¬ (A ∖ a₀)
isContr→isEmptyRemove = isProp→isEmptyRemove ∘ isContr→isProp
```

### Binary sums

Removing points from binary sums of types commutes with the constructor \( \mathsf{inl} \):
The type \( (A ∖ a) ⊎ B \) is equivalent to \( (A ⊎ B) ∖ \mathsf{inl}(a) \).
```agda
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
```

The same applies to \( \mathsf{inr} \).
```agda
remove-right-Iso : ∀ {b : B} → Iso (A ⊎ (B ∖ b)) ((A ⊎ B) ∖ (inr b))

remove-right-equiv : ∀ {b : B} → (A ⊎ (B ∖ b)) ≃ ((A ⊎ B) ∖ (inr b))
```
<!--
```agda
remove-right-Iso .Iso.fun (inl a) = inl a , Sum.inr≢inl
remove-right-Iso .Iso.fun (inr (b′ , b′≢b)) = inr b′ , b′≢b ∘ Sum.inrInj
remove-right-Iso .Iso.inv (inl a , _) = inl a
remove-right-Iso .Iso.inv (inr b′ , inr-b′≢inr-b) = inr (b′ , inr-b′≢inr-b ∘ cong inr)
remove-right-Iso .Iso.rightInv (inl a , _) = Remove≡ (refl′ (inl a))
remove-right-Iso .Iso.rightInv (inr b′ , _) = Remove≡ (refl′ (inr b′))
remove-right-Iso .Iso.leftInv (inl a) = refl′ (inl a)
remove-right-Iso .Iso.leftInv (inr (b′ , _)) = cong inr $ Remove≡ $ refl′ b′

remove-right-equiv = isoToEquiv remove-right-Iso
```
-->

### Dependent sums

Removing points from dependent sums is a little more subtle.
Intuitively, a point in \( \sum_{a : A} B(a) ∖ (a_0, b_0) \) should be one of the following:

- some \( (a, b) \) such that \( a \neq a_0 \) (i.e. a term of \( \sum_{a : A ∖ a_0} B(a) \)), or
- some \( b : B(a_0) \) such that \( b \neq b_0 \).

In general, we cannot decide \( a = a_0 \), but if there is at most one loop \( a_0 = a_0 \),
we can at least map the above alternatives into \( \sum_{a : A} B(a) ∖ (a_0, b_0) \).
```agda
module _ {B : A → Type ℓ} (a₀ : A) (b₀ : B a₀) (is-prop-a₀-loop : isProp (a₀ ≡ a₀)) where
  Σ-remove : (Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀) → (Σ A B ∖ (a₀ , b₀))
```

The first case is straightforward: \( a_0 \neq a \) implies \( (a_0, b_0) \neq (a, b) \).
```agda
  Σ-remove (inl ((a , a₀≢a) , b)) = (a , b) , goal where
    goal : (a₀ , b₀) ≢ (a , b)
    goal = a₀≢a ∘ cong fst
```
In the second case, we map \( b : B(a_0) \) to \( (a_0, b) \).
```agda
  Σ-remove (inr (b , b₀≢b)) = (a₀ , b) , goal where
```
We use the assumption \( \mathsf{isProp}(a_0 = a_0) \) to show that \( (a_0 , b_0) \neq (a_0 , b) \).
Assume \( (a_0 , b_0) = (a_0 , b) \).
```agda
    module _ (a₀b₀≡a₀b : (a₀ , b₀) ≡ (a₀ , b)) where
```
This means in particular \( p : a_0 = a_0 \) and \( q : b_0 =_{p} b \).
```agda
      a₀≡a₀ : a₀ ≡ a₀
      a₀≡a₀ = cong fst a₀b₀≡a₀b

      b₀≡ᴰb : PathP (λ i → B (a₀≡a₀ i)) b₀ b
      b₀≡ᴰb = cong snd a₀b₀≡a₀b
```
By assumption, \( p = \mathsf{refl} \), hence there is some \( q' : b_0 = b \).
```agda
      b₀≡b : b₀ ≡ b
      b₀≡b = subst (λ (p : a₀ ≡ a₀) → PathP (λ i → B (p i)) b₀ b) (is-prop-a₀-loop a₀≡a₀ refl) b₀≡ᴰb
```
But this is contradictory since we started with \( b_0 \neq b \).
```agda
      goal : Empty.⊥
      goal = b₀≢b b₀≡b
```

If, however, we get to assume that \( a_0 \) is isolated,
then `Σ-remove a₀` has an inverse ---
being able to decide \( a_0 = a \) for any \( a : A \) makes this possible.
```agda
module _ {B : A → Type ℓ} {a₀ : A} {b₀ : B a₀}
  (a₀≟_ : isIsolated a₀)
  where
```
Recall that there is at most one path to \( a_0 \) if it is isolated, hence
```agda
  private
    is-prop-a₀-loop : isProp (a₀ ≡ a₀)
    is-prop-a₀-loop = isIsolated→isPropPath a₀ a₀≟_ a₀
```
Abbreviate the map,
```agda
    Σ-remove' = Σ-remove {B = B} a₀ b₀ is-prop-a₀-loop
```
and construct its inverse as follows:
```agda
    Σ-remove-inv' : ∀ a → Dec (a₀ ≡ a) → (b : B a) → (a₀ , b₀) ≢ (a , b) → (Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀)
```
If \( p : a_0 = a \), then we can transport \( b : B(a) \) along this path to get some \( b' : B(a_0) \).
```agda
    Σ-remove-inv' a (yes a₀≡a) b neq = inr on-yes where
      b′ : B a₀
      b′ = subst⁻ B a₀≡a b
```
But if also \( (a_0, b_0) \neq (a, b) \), then necessarily \( b_0 \neq b' \).
```agda
      b₀≢b′ : b₀ ≢ b′
      b₀≢b′ q = neq goal where
        b₀≡ᴰb : PathP (λ i → B (a₀≡a i)) b₀ b
        b₀≡ᴰb = toPathP⁻ q

        goal : (a₀ , b₀) ≡ (a , b)
        goal = ΣPathP (a₀≡a , b₀≡ᴰb)
```
Therefore, we can map \( b : B(a) \) to \( b' : B(a_0) ∖ b_0 \).
```agda
      on-yes : B a₀ ∖ b₀
      on-yes = b′ , b₀≢b′
    Σ-remove-inv' a (no a₀≢a) b _ = inl ((a , a₀≢a) , b)
```
Uncurrying the above, we obtain:
```agda
  Σ-remove-inv : (Σ A B ∖ (a₀ , b₀)) → (Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀)
  Σ-remove-inv ((a , b) , neq) = Σ-remove-inv' a (a₀≟ a) b neq
```
With a bit of elbow grease, we can show that `Σ-remove-inv` is both a left- and right-inverse to `Σ-remove`.
```agda
  Σ-remove-rinv : ∀ a → (a₀≟a : Dec (a₀ ≡ a)) → (b : B a) → (neq : (a₀ , b₀) ≢ (a , b))
    → Σ-remove' (Σ-remove-inv' a a₀≟a b neq) ≡ ((a , b) , neq)
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
```

In particular, `Σ-remove` is an equivalence.
```agda
  isIsolatedFst→Σ-remove-equiv : ((Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀)) ≃ (Σ A B ∖ (a₀ , b₀))
  isIsolatedFst→Σ-remove-equiv = isoToEquiv Σ-remove-Iso

  isIsolatedFst→isEquiv-Σ-remove : isEquiv Σ-remove'
  isIsolatedFst→isEquiv-Σ-remove = equivIsEquiv isIsolatedFst→Σ-remove-equiv
```

### Connected types

```agda
module Connected where
  open import Cubical.Homotopy.Connected
  import      Cubical.HITs.Truncation as Tr
```

Since all operations we define have to have a continuous interpretation,
removal of points cannot be discontinuous.
In particular, \( A ∖ a_0 \) really is "\( A \) without the _connected component around \( a_0 \)_".
We can make this precise as follows:
If \( A \) is _connected_, then \( A ∖ a_0 \) is _empty_.
```agda
  isConnected→isEmptyRemove : isConnected h-set A → ∀ a₀ → ¬ (A ∖ a₀)
```
We can prove that having some \( a : A \) such that \( a_0 \neq a \) leads to a contradiction.
```agda
  isConnected→isEmptyRemove {A} 2-conn-A a₀ (a , a₀≢a) = contradiction where
```
Being connected means that, for any pair of points, there merely is a path between them.
In particular, there merely is a path \( a_0 = a \).
```agda
    1-conn-path : isConnected 1 (a₀ ≡ a)
    1-conn-path = isConnectedPath 1 2-conn-A _ _

    mere-path : Tr.∥ a₀ ≡ a ∥ 1
    mere-path = 1-conn-path .fst
```
But we assumed that \( a_0 \neq a \), hence the contradiction.
```agda
    contradiction : Empty.⊥
    contradiction = Tr.rec {n = 1} Empty.isProp⊥ a₀≢a mere-path
```

In general, connectivity levels are downward-closed,
and the same result holds for types of higher levels of connectivity.
```agda
  isConnected+2→isEmptyRemove : ∀ k → isConnected (k + 2) A → ∀ a₀ → ¬ (A ∖ a₀)
  isConnected+2→isEmptyRemove k = isConnected→isEmptyRemove ∘ isConnectedSubtr 2 k
```
