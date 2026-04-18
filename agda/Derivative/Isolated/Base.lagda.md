<!--
```agda
{-# OPTIONS -WnoUnsupportedIndexedMatch --safe #-}
module Derivative.Isolated.Base where

open import Derivative.Prelude
open import Derivative.Basics.Decidable
  as Dec
  using
    ( locallyDiscrete→locallyIsPropPath
    ; Dec ; yes ; no
    ; Discrete
    ; isProp¬
    )
open import Derivative.Basics.Embedding

open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv ; congEquiv)
open import Cubical.Relation.Nullary.Properties using (EquivPresDec ; EquivPresDiscrete)
open import Cubical.Relation.Nullary.HLevels using (isPropDiscrete)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

private
  variable
    ℓ : Level
    A B : Type ℓ
```
-->

# Isolated points of a type

A point `a : A` is isolated if `a ≡ b` is decidable for all `b : A`.
```agda
isIsolated : (a : A) → Type (ℓ-of A)
isIsolated a = ∀ b → Dec (a ≡ b)
```

## Isolated points form a discrete subtype

The identity types around isolated points are trivial:
there is at most one path to an isolated point.
```agda
isIsolated→isPropPath : (a : A) → isIsolated a → ∀ b → isProp (a ≡ b)
isIsolated→isPropPath = locallyDiscrete→locallyIsPropPath
```

Since `a ≡ b` is a proposition for any isolated `a`, `Dec (a ≡ b)` must be a proposition as well.
```agda
isIsolated→isPropDecPath : (a : A) → isIsolated a → ∀ b → isProp (Dec (a ≡ b))
isIsolated→isPropDecPath a isolated b = Dec.isPropDec (isIsolated→isPropPath a isolated b)
```

Therefore, being isolated is a proposition:
```agda
isPropIsIsolated : (a : A) → isProp (isIsolated a)
isPropIsIsolated a = isPropFromPointed→isProp go where
```

To show the above, it suffices to prove that if `a : A` is isolated, then `isIsolated a` is a proposition.
This follows from the general fact that to show that `P` is a proposition, we can assume that `P` is inhabited.
```agda
  go : isIsolated a → isProp (isIsolated a)
  go isolated = isPropΠ $ isIsolated→isPropDecPath a isolated
```

We write `Isolated A` or `A °` for the subtype of isolated points.
```agda
Isolated : (A : Type ℓ) → Type ℓ
Isolated A = Σ[ a ∈ A ] isIsolated a

_° : (A : Type ℓ) → Type ℓ
A ° = Isolated A

forget-isolated : A ° → A
forget-isolated = fst
```

By `isIsolated→isPropPath`, loops around an isolated point must be trivial.
In other words, isolated points satisfy a K-like rule.
```agda
module _ (a : A) (is-isolated-a : isIsolated a) where
  isIsolated→K : (p : a ≡ a) → p ≡ refl
  isIsolated→K p = isIsolated→isPropPath a is-isolated-a a p refl
  
  isIsolated→isContrLoop : isContr (a ≡ a)
  isIsolated→isContrLoop .fst = refl
  isIsolated→isContrLoop .snd = sym ∘ isIsolated→K
```

Since being isolated is a proposition, equality in `A °` is just that of `A`:
```agda
Isolated≡ : ∀ {a b : A °} → forget-isolated a ≡ forget-isolated b → a ≡ b
Isolated≡ = Σ≡Prop isPropIsIsolated
```

Of course, the same applies to dependent paths,
except that the type looks a little more unwieldly.
```agda
IsolatedPathP : ∀ {B : A → Type ℓ} {a₀ a₁ : A} {p : a₀ ≡ a₁}
  → {b₀ : B a₀ °} {b₁ : B a₁ °}
  → PathP (λ i → B (p i)) (b₀ .fst) (b₁ .fst)
  → PathP (λ i → B (p i) °) b₀ b₁
IsolatedPathP q i .fst = q i
IsolatedPathP {b₀} {b₁} q i .snd = isProp→PathP {B = λ i → isIsolated (q i)} (λ i → isPropIsIsolated (q i)) (b₀ .snd) (b₁ .snd) i
```

Inequality in `A °` always implies inequality in `A`.
```agda
Isolated≢ : ∀ {a b : A °} → forget-isolated a ≢ forget-isolated b → a ≢ b
Isolated≢ a≢b p = a≢b $ cong fst p
```

Together, this shows that `A °` is a discrete type:
For any pair `a, b : A °`, there is two ways of showing that `a ≡ b`,
either by using isolatedness of `a`, or of `b`.
```agda
DiscreteIsolated : Discrete (A °)
DiscreteIsolated (a , a≟_) (b , b≟_) = Dec.map Isolated≡ Isolated≢ (a≟ b)
```

By Hedberg's theorem, this implies that `A °` is an _h_-set:
```agda
_ : isSet (A °)
_ = Dec.Discrete→isSet DiscreteIsolated
```

For our developement, we chose to prove this more directly however.
```agda
opaque
  isSetIsolated : isSet (A °)
  isSetIsolated (a₀ , isolated-a₀) (a₁ , isolated-a₁) = isOfHLevelRespectEquiv 1 ΣPathP≃PathPΣ $ isPropΣ
    (isIsolated→isPropPath a₀ isolated-a₀ a₁)
    (λ p → isOfHLevelPathP 1 (isPropIsIsolated a₁) _ _)
```

In a discrete type `A`, every point is isolated by definition.
It follows that the forgetful map `A ° → A` is an equivalence.
```agda
module _ (_≟_ : Discrete A) where
  Discrete→isIsolated : ∀ a → isIsolated a
  Discrete→isIsolated = _≟_

  Discrete→isEquiv-forget-isolated : isEquiv {A = A °} forget-isolated
  Discrete→isEquiv-forget-isolated = equivIsEquiv $ Σ-contractSnd λ a → inhProp→isContr (Discrete→isIsolated a) (isPropIsIsolated a)

  Discrete→IsolatedEquiv : A ° ≃ A
  Discrete→IsolatedEquiv .fst = forget-isolated
  Discrete→IsolatedEquiv .snd = Discrete→isEquiv-forget-isolated
```

Conversely, if `forget-isolated : A ° → A` is an equivalence, then `A` must be discrete.
```agda
isEquiv-forget-isolated→Discrete : isEquiv {A = A °} forget-isolated → Discrete A
isEquiv-forget-isolated→Discrete is-equiv-forget = EquivPresDiscrete (forget-isolated , is-equiv-forget) DiscreteIsolated
```

Consequently, `forget-isolated : A ° → A` is an equivalence _if and only if_ `A` is discrete.
```agda
isEquiv-forget-isolated≃Discrete : isEquiv {A = A °} forget-isolated ≃ Discrete A
isEquiv-forget-isolated≃Discrete = propBiimpl→Equiv (isPropIsEquiv _) isPropDiscrete
  isEquiv-forget-isolated→Discrete
  Discrete→isEquiv-forget-isolated
```

A type is _perfect_ if it does not have any isolated points at all:
```agda
isPerfect : (A : Type ℓ) → Type ℓ
isPerfect A = ¬ (A °)
```

## Preservation of isolated points

Equivalences of types both preserve and reflect isolated points.
```agda
isIsolatedPreserveEquiv : (e : A ≃ B) → (a : A) → isIsolated a → isIsolated (equivFun e a)
isIsolatedPreserveEquiv e a isolated b = EquivPresDec (equivAdjointEquiv e) (isolated (invEq e b))

isIsolatedReflectEquiv : (e : A ≃ B) → (a : A) → isIsolated (equivFun e a) → isIsolated a
isIsolatedReflectEquiv e a isolated a′ = EquivPresDec (invEquiv (congEquiv e)) (isolated (equivFun e a′))

isIsolatedPreserveEquivInv : (e : A ≃ B) → (b : B) → isIsolated b → isIsolated (invEq e b)
isIsolatedPreserveEquivInv e b isolated a = EquivPresDec eqv (isolated (equivFun e a))
    where
    eqv : (b ≡ equivFun e a) ≃ (invEq e b ≡ a)
    eqv = symEquiv ∙ₑ invEquiv (equivAdjointEquiv e) ∙ₑ symEquiv

isIsolated≃isIsolatedEquivFun : (e : A ≃ B) → ∀ a → isIsolated a ≃ isIsolated (equivFun e a)
isIsolated≃isIsolatedEquivFun e a = propBiimpl→Equiv (isPropIsIsolated _) (isPropIsIsolated _)
  (isIsolatedPreserveEquiv e a)
  (isIsolatedReflectEquiv e a)
```

In particular, any equivalence induces an equivalence of isolated points.
```agda
IsolatedSubstEquiv : (e : A ≃ B) → A ° ≃ B °
IsolatedSubstEquiv e = Σ-cong-equiv e (isIsolated≃isIsolatedEquivFun e)
```

Equivalences are not the only maps that reflect isolated points.
Any injective map (in the naive sense of `f a ≡ f b → a ≡ b`) does so as well:
```agda
opaque
  InjReflectIsolated : (f : A → B) → (∀ a b → f a ≡ f b → a ≡ b) → ∀ {a} → isIsolated (f a) → isIsolated a
  InjReflectIsolated f inj-f {a} isolated-fa a′ =
    Dec.map
      (inj-f a a′)
      (λ fa≢fa′ a≡a′ → fa≢fa′ $ cong f a≡a′)
      (isolated-fa (f a′))
```

Of course, this also applies to _embeddings_, which are in general better behaved.
```agda
EmbeddingReflectIsolated : (f : A → B) → isEmbedding f → ∀ {a} → isIsolated (f a) → isIsolated a
EmbeddingReflectIsolated f emb-f = InjReflectIsolated f (isEmbedding→Inj emb-f)
```

If the embedding is _decidable_ (i.e. has decidable fibers), then it also creates isolated points.
```agda
DecEmbeddingCreateIsolated : (f : A → B) → isEmbedding f → (∀ b → Dec (fiber f b)) → ∀ {a} → isIsolated a → isIsolated (f a)
DecEmbeddingCreateIsolated f emb-f dec-fib {a} isolated-a b with (dec-fib b)
... | (yes (a′ , fa′≡b)) = Dec.map (λ a≡a′ → cong f a≡a′ ∙ fa′≡b) (λ a≢a′ fa≡b → a≢a′ (isEmbedding→Inj emb-f _ _ (fa≡b ∙ sym fa′≡b))) (isolated-a a′)
... | (no ¬fib) = no (¬fib ∘ (a ,_))
```

Isolated points are preserved by transport and `subst`:
```agda
opaque
  isIsolatedTransport : (a : A) (p : A ≡ B) → isIsolated a → isIsolated (transport p a)
  isIsolatedTransport a = J (λ B p → isIsolated a → isIsolated (transport p a)) λ where
    isolated-a a′ → subst (λ - → Dec (- ≡ a′)) (sym $ transportRefl a) (isolated-a a′)

  isIsolatedSubst : (B : A → Type ℓ) {x y : A} (p : x ≡ y)
    → {b : B x}
    → isIsolated b
    → isIsolated (subst B p b)
  isIsolatedSubst B p {b} = isIsolatedTransport b (cong B p)
```

This lets us restrict `subst` to isolated points:
```agda
subst° : (B : A → Type ℓ) {x y : A} (p : x ≡ y) → B x ° → B y °
subst° B p (b , isolated-b) .fst = subst B p b
subst° B p (b , isolated-b) .snd = isIsolatedSubst B p isolated-b
```

## Isolatedness for low truncation levels

In a proposition, every point is trivially isolated:
The answer to the question "Does a ≡ b?" in a proposition is always "yes".
```agda
isProp→isIsolated : isProp A → (a : A) → isIsolated a
isProp→isIsolated prop-A a b = yes $ prop-A a b

isProp→IsolatedEquiv : ∀ {P : Type ℓ} → isProp P → (P °) ≃ P
isProp→IsolatedEquiv = Discrete→IsolatedEquiv ∘ Dec.isProp→Discrete
```

In turn, all points of a contractible type must be isolated.
```agda
isContr→isIsolatedCenter : isContr A → (a : A) → isIsolated a
isContr→isIsolatedCenter = isProp→isIsolated ∘ isContr→isProp
```

<!--
```agda
-- Yeah, that's a pity:
DecIsolated→DecProp : (∀ (A : Type ℓ) → Dec (Isolated A)) → ∀ P → isProp P → Dec P
DecIsolated→DecProp all-dec P is-prop-P = Dec.map forget-isolated nope (all-dec P)
  where
    nope : ¬ (P °) → ¬ P
    nope heck-no p = heck-no (invEq (isProp→IsolatedEquiv is-prop-P) p)
```
-->

Conversely, the connected component around an isolated point `a : A °` (that is, all `b : A` merely equal to `a`)
is contractible:
```agda
isIsolated→isContrConnectedComponent : {a : A} → isIsolated a → isContr (Σ[ a′ ∈ A ] ∥ a ≡ a′ ∥₁)
isIsolated→isContrConnectedComponent {A} {a} a≟_ = isOfHLevelRespectEquiv 0 singl-equiv (isContrSingl a) where
  singl-equiv : singl a ≃ (Σ[ a′ ∈ A ] ∥ a ≡ a′ ∥₁)
  singl-equiv = Σ-cong-equiv-snd λ a′ → invEquiv (PT.propTruncIdempotent≃ (isIsolated→isPropPath a a≟_ a′))
```

<!--
```agda
-- TODO: In a perfect type, no connecte component is contractible.
-- isPerfect→¬isContrConnectedComponent : isPerfect A → ∀ a → ¬ isContr (Σ[ b ∈ A ] ∥ a ≡ b ∥₁)
-- isPerfect→¬isContrConnectedComponent {A} is-perfect a is-contr-conn = is-perfect (a , is-isolated-a) where
--   is-isolated-a : isIsolated a
--   is-isolated-a b = yes {! isContr→isProp is-contr-conn (a , ?) !}
```
-->
