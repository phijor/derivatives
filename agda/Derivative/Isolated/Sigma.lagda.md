<!--
```agda
{-# OPTIONS --safe #-}
module Derivative.Isolated.Sigma where

open import Derivative.Prelude
open import Derivative.Basics.Decidable as Dec
open import Derivative.Basics.Embedding

open import Derivative.Isolated.Base

open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv)
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

private
  variable
    ℓ : Level
    A : Type ℓ
    B : A → Type ℓ
```
-->

# Isolated points of _Σ_-types

If `a : A` and `b : B a` are isolated, then `(a , b)` is isolated in `Σ A B`.
```agda
isIsolatedΣ : ∀ {a : A} {b : B a}
  → isIsolated a
  → isIsolated b
  → isIsolated {A = Σ A B} (a , b)
isIsolatedΣ {B} {a} {b} isolated-a isolated-b (a′ , b′) = discrete (isolated-a a′) where
  discrete : Dec (a ≡ a′) → Dec ((a , b) ≡ (a′ , b′))
  discrete (yes p) = Dec.decEquiv (ΣPathTransport≃PathΣ _ _) (discrete-b (isolated-b _)) where
    adj : {p : a ≡ a′} → (subst B p b ≡ b′) ≃ (b ≡ subst B (sym p) b′)
    adj {p} = substAdjointEquiv B p

    discrete-b : Dec (b ≡ subst B (sym p) b′) → Dec (Σ[ p ∈ a ≡ a′ ] subst B p b ≡ b′)
    discrete-b (yes q) = yes (p , invEq adj q)
    discrete-b (no ¬q) = no λ { (p , q) → ¬q (equivFun adj $ cong (λ p → subst B p b) (isIsolated→isPropPath a isolated-a a′ _ _) ∙ q) }
    
  discrete (no ¬p) = no λ r → ¬p (cong fst r)
```

This defines a map from pairs of isolated points to isolated pairs:
```agda
Σ-isolate : ∀ {ℓA ℓB} (A : Type ℓA) (B : A → Type ℓB)
  → (Σ[ a° ∈ A ° ] (B (a° .fst)) °) → (Σ[ a ∈ A ] B a) °
Σ-isolate A B ((a , isolated-a) , b , isolated-b) .fst .fst = a
Σ-isolate A B ((a , isolated-a) , b , isolated-b) .fst .snd = b
Σ-isolate A B ((a , isolated-a) , b , isolated-b) .snd = isIsolatedΣ isolated-a isolated-b

_,°_ : (a : A °) → (b : B (a .fst) °) → (Σ[ a ∈ A ] B a) °
a ,° b = Σ-isolate _ _ (a , b)
```

## Characterizing `Σ-isolate`

A prori, it is not clear whether `Σ-isolate` is an equivalence or not.
We can however reshape its fibers into a proposition:
```agda
Σ-isolate-fiber-equiv : ∀ (A : Type ℓ) (B : A → Type ℓ)
  → (a : A) (b : B a) (isolated-ab : isIsolated {A = Σ A B} (a , b))
  → fiber (Σ-isolate A B) ((a , b) , isolated-ab) ≃ (isIsolated a × isIsolated b)
Σ-isolate-fiber-equiv A B a b isolated-ab =
  (Σ[ ((a′ , _) , (b′ , _)) ∈ Σ[ (a , _) ∈ A ° ] B a ° ] ((a′ , b′) , _) ≡ _)
    ≃⟨ Σ-cong-equiv-snd (λ _ → invEquiv $ Σ≡PropEquiv isPropIsIsolated) ⟩
  (Σ[ ((a′ , _) , (b′ , _)) ∈ Σ[ (a , _) ∈ A ° ] B a ° ] (a′ , b′) ≡ (a , b))
    ≃⟨ Σ-cong-equiv-snd (λ _ → invEquiv ΣPathP≃PathPΣ) ⟩
  (Σ[ ((a′ , _) , (b′ , _)) ∈ Σ[ (a , _) ∈ A ° ] B a ° ] Σ[ p ∈ a′ ≡ a ] PathP (λ i → B (p i)) b′ b)
    ≃⟨ strictEquiv
      (λ { (((a′ , h-a′) , (b′ , h-b′)) , p , pᴰ) → ((a′ , sym p) , (b′ , symP pᴰ) , (h-a′ , h-b′)) })
      (λ { ((a′ , p) , (b′ , pᴰ) , (h-a′ , h-b′)) → (((a′ , h-a′) , (b′ , h-b′)) , sym p , symP pᴰ) })
    ⟩
  (Σ[ (a′ , p) ∈ singl a ] Σ[ (b′ , pᴰ) ∈ singlP (λ i → B (p i)) b ] isIsolated a′ × isIsolated b′)
    ≃⟨ Σ-contractFst (isContrSingl a) ⟩
  (Σ[ (b′ , pᴰ) ∈ singl b ] isIsolated a × isIsolated b′)
    ≃⟨ Σ-contractFst (isContrSingl b) ⟩
  (isIsolated a × isIsolated b)
    ≃∎

isProp-fiber-Σ-isolate : ∀ (A : Type ℓ) (B : A → Type ℓ)
  → ∀ y → isProp (fiber (Σ-isolate A B) y)
isProp-fiber-Σ-isolate A B y = isOfHLevelRespectEquiv 1 (invEquiv $ Σ-isolate-fiber-equiv A B _ _ _)
  $ isProp× (isPropIsIsolated _) (isPropIsIsolated _)

```

This shows that `Σ-isolate` is an embedding:
```agda
isEmbedding-Σ-isolate : ∀ (A : Type ℓ) (B : A → Type ℓ) → isEmbedding (Σ-isolate A B)
isEmbedding-Σ-isolate A B = hasPropFibers→isEmbedding $ isProp-fiber-Σ-isolate A B

Σ-isolate-embedding : ∀ (A : Type ℓ) (B : A → Type ℓ)
  → (Σ[ a° ∈ A ° ] (B (a° .fst)) °) ↪ ((Σ[ a ∈ A ] B a) °)
Σ-isolate-embedding A B .fst = Σ-isolate A B
Σ-isolate-embedding A B .snd = isEmbedding-Σ-isolate A B
```

If `Σ-isolate` is an equivalence, then we get a converse to `isIsolatedΣ`:
```agda
module _
  {A : Type ℓ} {B : A → Type ℓ}
  (is-equiv-Σ-isolate : isEquiv (Σ-isolate A B))
  where
  isEquiv-Σ-isolate→isIsolatedPair : {a₀ : A} {b₀ : B a₀} → isIsolated {A = Σ A B} (a₀ , b₀) → isIsolated a₀ × isIsolated b₀
  isEquiv-Σ-isolate→isIsolatedPair {a₀} {b₀} isolated-ab = equivFun (Σ-isolate-fiber-equiv A B a₀ b₀ isolated-ab) fib where
    fib : fiber (Σ-isolate A B) ((a₀ , b₀) , isolated-ab)
    fib = is-equiv-Σ-isolate .equiv-proof ((a₀ , b₀) , isolated-ab) .fst

  isEquiv-Σ-isolate→isIsolatedFst : {a₀ : A} {b₀ : B a₀} → isIsolated {A = Σ A B} (a₀ , b₀) → isIsolated a₀
  isEquiv-Σ-isolate→isIsolatedFst = fst ∘ isEquiv-Σ-isolate→isIsolatedPair
```

Since `Σ-isolate` is always an embedding, it being an equivalence is the same as it being surjective.
```agda
isEquiv-Σ-isolate≃isSurjection-Σ-isolate : (A : Type ℓ) (B : A → Type ℓ) → isEquiv (Σ-isolate A B) ≃ isSurjection (Σ-isolate A B)
isEquiv-Σ-isolate≃isSurjection-Σ-isolate A B =
  isEquiv _
    ≃⟨ isEquiv≃isEquiv' _ ⟩
  (∀ y → isContr (fiber (Σ-isolate A B) y))
    ≃⟨ equivΠCod (λ y → isContr≃mereInh×isProp) ⟩
  (∀ y → ∥ fiber _ y ∥₁ × isProp (fiber _ y))
    ≃⟨ equivΠCod (λ y → Σ-contractSnd λ _ → inhProp→isContr (isProp-fiber-Σ-isolate _ _ y) isPropIsProp) ⟩
  (∀ y → ∥ fiber _ y ∥₁)
    ≃∎
```

Thus we can strengthen `isEquiv-Σ-isolate→isIsolatedPair` to the following equivalence:
```agda
isSurjection-Σ-isolate≃isIsolatedPair : (A : Type ℓ) (B : A → Type ℓ)
  → isSurjection (Σ-isolate A B) ≃ (∀ a → (b : B a) → isIsolated {A = Σ A B} (a , b) → isIsolated a × isIsolated b)
isSurjection-Σ-isolate≃isIsolatedPair A B =
  (∀ y → ∥ fiber _ y ∥₁)
    ≃⟨ equivΠCod (λ y → PT.propTruncIdempotent≃ (isProp-fiber-Σ-isolate _ _ y))  ⟩
  (∀ y → fiber _ y)
    ≃⟨ curryEquiv ⟩
  ((a,b : Σ A B) → (h : isIsolated a,b) → fiber (Σ-isolate A B) (a,b , h))
    ≃⟨ curryEquiv ⟩
  ((a : A) (b : B a) (h : isIsolated (a , b)) → fiber (Σ-isolate A B) ((a , b) , h))
    ≃⟨ equivΠCod (λ a → equivΠCod λ b → equivΠCod λ h → Σ-isolate-fiber-equiv A B a b h) ⟩
  ((a : A) (b : B a) → isIsolated (a , b) → isIsolated a × isIsolated b)
    ≃∎
```

By composing both equivalences, we see `Σ-isolate` is an equivalence if and only of isolatedness distributes over `Σ`.
```agda
isEquiv-Σ-isolate≃isIsolatedPair : (A : Type ℓ) (B : A → Type ℓ)
 → isEquiv (Σ-isolate A B) ≃ (∀ (a₀ : A) (b₀ : B a₀) → isIsolated {A = Σ A B} (a₀ , b₀) → isIsolated a₀ × isIsolated b₀)
isEquiv-Σ-isolate≃isIsolatedPair A B = isEquiv-Σ-isolate≃isSurjection-Σ-isolate A B ∙ₑ isSurjection-Σ-isolate≃isIsolatedPair A B
```

## Discreteness and _Σ_-types

If `A : Type` is discrete, and `B : A → Type` is family of discrete types, then
`Σ-isolate` is an equivalence.
This follows from the closure of discrete types under `Σ`:
```agda
Discrete→isEquiv-Σ-isolate : Discrete A → (∀ a → Discrete (B a)) → isEquiv (Σ-isolate A B)
Discrete→isEquiv-Σ-isolate {A} {B} disc-A disc-B = subst isEquiv compute (equivIsEquiv e) where
  e : (Σ[ a° ∈ A ° ] (B (a° .fst)) °) ≃ ((Σ[ a ∈ A ] B a) °)
  e =
    Σ[ a° ∈ A ° ] (B (a° .fst)) °
      ≃⟨ Σ-cong-equiv (Discrete→IsolatedEquiv disc-A) (Discrete→IsolatedEquiv ∘ disc-B ∘ fst) ⟩
    Σ[ a ∈ A ] B a
      ≃⟨ invEquiv (Discrete→IsolatedEquiv (discreteΣ disc-A disc-B)) ⟩
    (Σ[ a ∈ A ] B a) °
      ≃∎

  compute : equivFun e ≡ Σ-isolate A B
  compute = funExt λ _ → Isolated≡ refl
```

If `a₀ : A` is an isolated point, then `(λ b → a₀ , b) : B a₀ → Σ A B` is an embedding.
This is not true for arbitrary points of `A`.
```agda
isIsolated→isEmbeddingInjSnd : (a₀ : A) → isIsolated a₀ → isEmbedding {A = B a₀} {B = Σ A B} (a₀ ,_)
isIsolated→isEmbeddingInjSnd {A} {B} a₀ is-isolated-a₀ = λ b₀ b₁ → equivIsEquiv $ isoToEquiv (path-iso b₀ b₁) where
  path-iso : (b₀ b₁ : B a₀) → Iso (b₀ ≡ b₁) ((a₀ , b₀) ≡ (a₀ , b₁))
  path-iso b₀ b₁ =
    (b₀ ≡ b₁)
      Iso⟨ invIso (Σ-contractFstIso (isIsolated→isContrLoop a₀ is-isolated-a₀)) ⟩
    Σ[ p ∈ a₀ ≡ a₀ ] PathP (λ i → B (p i)) b₀ b₁
      Iso⟨ ΣPathPIsoPathPΣ {B = λ i → B} ⟩
    ((a₀ , b₀) ≡ (a₀ , b₁))
      ∎Iso
```

Thus, over an isolated point `a₀ : A`, a point `b : B a₀` is isolated if the pair `(a₀ , b)` is isolated.
```agda
isIsolatedFst→isIsolatedSnd≃isIsolatedPair : {a₀ : A} → isIsolated a₀ → (b₀ : B a₀) → isIsolated b₀ ≃ isIsolated {A = Σ A B} (a₀ , b₀)
isIsolatedFst→isIsolatedSnd≃isIsolatedPair {A} {B} {a₀} isolated-a₀ b₀ = propBiimpl→Equiv
  (isPropIsIsolated b₀)
  (isPropIsIsolated (a₀ , b₀))
  (isIsolatedΣ isolated-a₀)
  (EmbeddingReflectIsolated (a₀ ,_) $ isIsolated→isEmbeddingInjSnd a₀ isolated-a₀)
```

We can also characterize discreteness of some type `A : Type` by how `Σ-isolate` behaves with respect to any family `B : A → Type`.
First, we can show that a type is discrete if `a₀ ,_ : B a₀ → Σ A B` reflects isolated points for any `a₀ : A` (not just isolated points):
```agda
isIsolatedΣSnd→Discrete : {ℓ : Level}
  → (A : Type ℓ)
  → ((B : A → Type ℓ) → (a₀ : A) → (b₀ : B a₀) → isIsolated {A = Σ A B} (a₀ , b₀) → isIsolated a₀)
  → Discrete A
isIsolatedΣSnd→Discrete {ℓ} A Σ-isolated-fst a₀ a₁ = goal where
  B' : A → Type ℓ
  B' a = a₀ ≡ a

  b₀ : B' a₀
  b₀ = refl

  is-isolated-pair : isIsolated {A = Σ A B'} (a₀ , b₀)
  is-isolated-pair = isContr→isIsolatedCenter (isContrSingl a₀) (a₀ , b₀)

  goal : Dec (a₀ ≡ a₁)
  goal = Σ-isolated-fst B' a₀ b₀ is-isolated-pair a₁
```

From this we can deduce that for all `A : Type`,
if `Σ-isolate` is an equivalence for _all_ families over `A`,
then `A` must be discrete.
```agda
isEquiv-Σ-isolate→DiscreteFst : (A : Type ℓ)
  → ((B : A → Type ℓ) → isEquiv (Σ-isolate A B))
  → Discrete A
isEquiv-Σ-isolate→DiscreteFst {ℓ} A is-equiv-Σ-isolate = isIsolatedΣSnd→Discrete A goal where
  goal : ∀ (B : A → Type ℓ) a₀ (b₀ : B a₀) → isIsolated (a₀ , b₀) → isIsolated a₀
  goal B a₀ b₀ isolated-ab = isEquiv-Σ-isolate→isIsolatedFst (is-equiv-Σ-isolate B) isolated-ab
```

The converse holds as well, since `a₀ ,_` is an embedding.
```agda
DiscreteFst→isEquiv-Σ-isolated : (A : Type ℓ)
  → Discrete A
  → ((B : A → Type ℓ) → isEquiv (Σ-isolate A B))
DiscreteFst→isEquiv-Σ-isolated A disc-A B = invEq (isEquiv-Σ-isolate≃isIsolatedPair _ _) proof where
  proof : ∀ a₀ → (b₀ : B a₀) → isIsolated (a₀ , b₀) → isIsolated a₀ × isIsolated b₀
  proof a₀ b₀ isolated-ab .fst = disc-A a₀
  proof a₀ b₀ isolated-ab .snd = EmbeddingReflectIsolated
    (a₀ ,_)
    (isIsolated→isEmbeddingInjSnd a₀ (disc-A a₀))
    isolated-ab
```

All together, a type `A` is discrete if and only if `Σ-isolate` is an equivalence for any family over `A`.
```agda
isEquiv-Σ-isolate≃DiscreteFst : (A : Type ℓ) → ((B : A → Type ℓ) → isEquiv (Σ-isolate A B)) ≃ Discrete A
isEquiv-Σ-isolate≃DiscreteFst A = propBiimpl→Equiv (isPropΠ λ B → isPropIsEquiv _) isPropDiscrete
  (isEquiv-Σ-isolate→DiscreteFst A)
  (DiscreteFst→isEquiv-Σ-isolated A)
```

We can restrict the above to a specific family: `A` is discrete if and only if `Σ-isolate` is an equivalence
for `A` and the family `a₀ ≡_ : A → Type`:
```agda
isEquiv-Σ-isolate-singl→Discrete : (∀ a₀ → isEquiv (Σ-isolate A (a₀ ≡_))) → Discrete A
isEquiv-Σ-isolate-singl→Discrete is-equiv-Σ-isolate a₀ = isolated-a₀ where
  is-isolated-center : isIsolated {A = singl a₀} (a₀ , refl)
  is-isolated-center = isContr→isIsolatedCenter (isContrSingl a₀) (a₀ , refl)

  isolated-a₀ : isIsolated a₀
  isolated-a₀ = isEquiv-Σ-isolate→isIsolatedFst (is-equiv-Σ-isolate a₀) is-isolated-center

Discrete→isEquiv-Σ-isolate-singl : Discrete A → (a₀ : A) → isEquiv (Σ-isolate A (a₀ ≡_))
Discrete→isEquiv-Σ-isolate-singl {A} disc-A a₀ = Discrete→isEquiv-Σ-isolate disc-A disc-a₀≡a where
  disc-a₀≡a : (a : A) → Discrete (a₀ ≡ a)
  disc-a₀≡a = Dec.Discrete→DiscretePath disc-A a₀

Discrete≃isEquiv-Σ-isolate-singl : Discrete A ≃ ((a₀ : A) → isEquiv (Σ-isolate A (a₀ ≡_)))
Discrete≃isEquiv-Σ-isolate-singl = propBiimpl→Equiv
  isPropDiscrete
  (isPropΠ λ a₀ → isPropIsEquiv _)
  Discrete→isEquiv-Σ-isolate-singl
  isEquiv-Σ-isolate-singl→Discrete
```
