# Overview

```agda
{-# OPTIONS --safe #-}
```

## Basic notation and definitions

```agda
open import Derivative.Prelude
```

<!--
```agda
module README where

open import Derivative.Basics.Decidable
open import Derivative.Basics.Embedding
open import Derivative.Basics.Equiv
open import Derivative.Basics.Maybe
open import Derivative.Basics.Sum
open import Derivative.Basics.Unit
open import Derivative.Basics.W

open import Cubical.Data.Nat.Base
open import Cubical.Functions.Surjection
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor hiding (_$_)

open UnitCounit

private
  variable
    ℓ : Level
    A B : Type ℓ
    a : A
    Ix : Type
```
-->

## Removing Isolated Points in Univalent Foundations

### Isolated points

```agda
open import Derivative.Isolated
```

**Definition 2.1**: Isolated points.
```agda
_ : (a : A) → Type _
_ = isIsolated
```

**Lemma 2.2**: Isolated points have propositional paths.
```agda
_ : (a : A) → isIsolated a → (b : A) → isProp (a ≡ b)
_ = isIsolated→isPropPath
```

**Corollary 2.3**: Being isolated is a proposition.
```agda
_ : (a : A) → isProp (isIsolated a)
_ = isPropIsIsolated
```

**Proposition 2.4**: Isolated points form a set.
```agda
_ : isSet (A °)
_ = isSetIsolated
```

**Lemma 2.5**:
Equivalences preserve and reflect isolated points, hence induce an equivalence.
```agda
_ : (e : A ≃ B) → ∀ a → isIsolated a ≃ isIsolated (equivFun e a)
_ = isIsolated≃isIsolatedEquivFun
```

This induces an equivalence on sets of isolated points:
```agda
_ : (e : A ≃ B) → A ° ≃ B °
_ = IsolatedSubstEquiv
```

**Proposition 2.6**:
Embeddings reflect isolated points.
```agda
_ : (f : A → B) → isEmbedding f → ∀ {a} → isIsolated (f a) → isIsolated a
_ = EmbeddingReflectIsolated
```

**Proposition 2.7**:
The constructors \( \mathsf{inl} : A → A ⊎ B \) and \( \mathsf{inr} : B → A ⊎ B \) preserve and reflect isolated points.
```agda
_ : ∀ {a : A} → isIsolated a ≃ isIsolated (inl {B = B} a)
_ = isIsolated≃isIsolatedInl

_ : ∀ {b : B} → isIsolated b ≃ isIsolated (inr {A = A} b)
_ = isIsolated≃isIsolatedInr
```

**Problem 2.8**:
The above induces an equivalence that distributes isolated points over binary sums:
```agda
_ : (A ⊎ B) ° ≃ (A °) ⊎ (B °)
_ = IsolatedSumEquiv
```

The type \( A ⊎ 𝟙 \) is used so often that we abbreviate it as \( \mathsf{Maybe}(A) \):
```agda
_ : (A : Type) → Maybe A ≡ (A ⊎ 𝟙)
_ = λ A → refl
```

The point \( \mathsf{nothing} : \mathsf{Maybe}(A) \) is always isolated:
```agda
_ : isIsolated {A = Maybe A} nothing
_ = isIsolatedNothing

_ : (Maybe A) °
_ = nothing°
```

**Corollary 2.9**:
The isolated points of \( \mathsf{Maybe}(A) \) are the isolated points of \( A \) and \( \mathsf{nothing} \):
```agda
_ : (A : Type) → (Maybe A) ° ≃ Maybe (A °)
_ = λ A →
  (Maybe A) °     ≃⟨ IsolatedSumEquiv ⟩
  (A °) ⊎ (𝟙 °) ≃⟨ ⊎-right-≃ (isProp→IsolatedEquiv isProp-𝟙*) ⟩
  Maybe (A °)     ≃∎
```

<!--
```agda
module _ (A : Type) (B : A → Type) where
```
-->

**Proposition 2.10**:
There is a map taking (dependent) pairs of isolated points to an
isolated point in the corresponding type of pairs:
```agda
  _ : (Σ[ (a , _) ∈ A ° ] (B a) °) → (Σ[ a ∈ A ] B a) °
  _ = Σ-isolate A B
```

**Proposition 2.11, Proposition 2.12**:
The fibers of this map are propositions, hence it is an embedding.
```agda
  _ : (a : A) (b : B a) (h : isIsolated {A = Σ A B} (a , b))
    → fiber (Σ-isolate A B) ((a , b) , h) ≃ (isIsolated a × isIsolated b)
  _ = Σ-isolate-fiber-equiv A B

  _ : isEmbedding (Σ-isolate A B)
  _ = isEmbedding-Σ-isolate A B
```

**Lemma 2.13**:
`Σ-isolate` is a surjection (hence an equivalence) iff pairing `(_,_)` reflects isolated points.
```agda
  _ : isSurjection (Σ-isolate A B) ≃ (∀ a → (b : B a) → isIsolated {A = Σ A B} (a , b) → isIsolated a × isIsolated b)
  _ = isSurjection-Σ-isolate≃isIsolatedPair A B
```

**Corollary 2.14**:
Over discrete types, `Σ-isolate` is an equivalence.
```agda
  _ : Discrete A → (∀ a → Discrete (B a)) → isEquiv (Σ-isolate A B)
  _ = Discrete→isEquiv-Σ-isolate
```

**Proposition 2.15**:
Over a fixed *isolated* point \( a_0 : A \), pairing \( λ b.\, (a_0 , b) \) preserves and reflects isolated points.
```agda
  _ : {a₀ : A} → isIsolated a₀ → (b₀ : B a₀) → isIsolated b₀ ≃ isIsolated {A = Σ A B} (a₀ , b₀)
  _ = isIsolatedFst→isIsolatedSnd≃isIsolatedPair
```

**Proposition 2.16**:
Discreteness of a type can be characterized by `Σ-isolate` at the family \( B(a) ≔ (a_0 = a) \).
```agda
_ : Discrete A ≃ ((a₀ : A) → isEquiv (Σ-isolate A (a₀ ≡_)))
_ = Discrete≃isEquiv-Σ-isolate-singl
```

### Removing points
```agda
open import Derivative.Remove
```

The type \( A ∖ a_0 \) is the subtype of \( A \) with \( a_0 \) removed.
```agda
_ : (A : Type) → (a₀ : A) → (A ∖ a₀) ≡ (Σ[ a ∈ A ] a₀ ≢ a)
_ = λ A a → refl
```

**Problem 2.17**:
Show that first adding a point to \( A \), then removing it gives a type equivalent to \( A \).
```agda
_ : Maybe A ∖ nothing ≃ A
_ = removeNothingEquiv
```

**Problem 2.18**:
More generally, removing a point from a binary sum is equivalent to
first removing the point from either side, then taking the sum.
```agda
_ : ∀ {a : A} → ((A ∖ a) ⊎ B) ≃ ((A ⊎ B) ∖ (inl a))
_ = remove-left-equiv

_ :  ∀ {b : B} → (A ⊎ (B ∖ b)) ≃ ((A ⊎ B) ∖ (inr b))
_ = remove-right-equiv
```

The other way around, there is a map that takes \( \mathsf{Maybe}(A ∖ a_0) \) and replaces \( \mathsf{nothing} \) with \( a_0 \):
```agda
_ : (a₀ : A) → Maybe (A ∖ a₀) → A
_ = replace
```

**Proposition 2.19**:
The map \( \mathsf{replace}(a_0) \) is an equivalence if and only if \( a_0 \) is isolated.
```agda
_ : (a₀ : A) → isIsolated a₀ ≃ isEquiv (replace a₀)
_ = isIsolated≃isEquiv-replace
```

<!--
```agda
module _ (A : Type) (B : A → Type) where
```
-->

**Problem 2.20**:
If \( a_0 \) is *h-isolated* (i.e. \( \mathsf{isProp}(a_0 = a_0) \)), then there is a map that
looks like it characterizes removal of points from \( Σ \)-types.
```agda
  _ : ∀ (a₀ : A) (b₀ : B a₀)
    → (isProp (a₀ ≡ a₀))
    → (Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀) → (Σ A B ∖ (a₀ , b₀))
  _ = Σ-remove
```

**Proposition 2.21**:
If `a₀` is isolated, then it is *h-isolated*, and `Σ-remove a₀ b₀` is an equivalence.
```agda
  _ : ∀ {a₀ : A} {b₀ : B a₀} → (h : isIsolated a₀) → isEquiv (Σ-remove {B = B} a₀ b₀ _)
  _ = isIsolatedFst→isEquiv-Σ-remove
```

### Grafting

**Problem 2.22**:
For all \( a : A^\circ \), *grafting* extends the domain of a function \( f : A \setminus a_0 \to B \) to all of \( A \), given some \( b_0 : B \).
```agda
_ : (a : A °) → (((A ∖° a) → B) × B) → (A → B)
_ = graft
```

**Proposition 2.23**:
This defines an *induction-like* principle for maps out of types \( A \) with an isolated point \( a_0 : A^\circ \).
In particular, it has computation rules,
```agda
_ : (a° : A °) (f : (A ∖° a°) → B) {b₀ : B} → graft a° (f , b₀) (a° .fst) ≡ b₀
_ = graft-β-yes

_ : (a° : A °) (f : (A ∖° a°) → B) {b₀ : B} (a : A ∖° a°) → graft a° (f , b₀) (a .fst) ≡ f a
_ = graft-β-no
```

Grafting for dependent functions is defined in:
```agda
import Derivative.Isolated.DependentGrafting
```

??? note
    We do not use this more general definition as it contains an extra `transport`,
    which, for non-dependent functions, is a transport over `refl`.
    Since `transport refl` does not definitionally reduce to the identity function,
    we would have to manually get rid of it everywhere.

## Derivatives of Containers

```agda
open import Derivative.Container
```

**Definition 3.1**:
A container \( (S ◁ P) \) consists of shapes \( S : \mathsf{Type} \) and a family of positions \( P : S → \mathsf{Type} \) over those shapes.
```agda
_ : (ℓ : Level) → Type (ℓ-suc ℓ)
_ = λ ℓ → Container ℓ ℓ

_ : (S : Type) → (P : S → Type) → Container _ _
_ = λ S P → (S ◁ P)
```

We sometimes use the notation \( (s : S \lhd P(s)) \) when defining containers.
```agda
_ : (S : Type) (P : S → Type) → Container _ _
_ = λ S P → (s ∈ S ◁ P s)
```
We use `∈` instead of `:`, as the latter is part of Agda's syntax.
This mirrors the notation `Σ[ a ∈ A ] B a` for `Σ A B`.

??? note "Universe polymorphism"
    Containers are defined for shapes and positions in any universe.
    For most constructions, we consider containers at a fixed level `ℓ`,
    that is the type `Container ℓ ℓ`.
    Some examples consider containers with large shapes (i.e. `Container (ℓ-suc ℓ) ℓ`), but this is mostly for convenience.
    The shapes of those containers could be resized to a type at level `ℓ`.

<!--
```agda
open Container
open _⊸_
private
  variable
    F G : Container ℓ-zero ℓ-zero
```
-->

**Definition 3.2**:
A linear morphism of containers consists of a map of shapes,
and a family of equivalences of positions.
```agda
_ : F ⊸ G ≃ (Σ[ fₛₕ ∈ (F .Shape → G .Shape) ] ∀ s → G .Pos (fₛₕ s) ≃ F .Pos s)
_ = ⊸-Σ-equiv
```

**Definition 3.3**:
A morphism is an equivalence of containers if its shape map is an equivalence of types.
We bundle this into a record.
```agda
_ : (F G : Container _ _) → Type ℓ-zero
_ = Equiv
```

Containers and linear morphisms assemble into a wild category.
Set-truncated containers form a 1-category.
```agda
open import Derivative.Category ℓ-zero
  renaming (∂ to ∂ₛ)

_ : WildCat _ _
_ = ℂont⊸∞

_ : Category _ _
_ = ℂont⊸
```

**Definition 3.4**:
An \( (n, k) \)-truncated container has \( n \)-truncated shapes, and \( k \)-truncated positions.
```agda
_ : (n k : HLevel) → (F : Container _ _) → Type _
_ = isTruncatedContainer {ℓS = ℓ-zero} {ℓP = ℓ-zero}
```

**Lemma 3.5**:
Extensionality for morphisms says that we can compare them by their shape- and position maps.
```agda
_ : (f g : F ⊸ G)
  → (Σ[ p ∈ f .shape ≡ g .shape ] (PathP (λ i → ∀ s → G .Pos (p i s) ≃ F .Pos s) (f .pos) (g .pos))) ≃ (f ≡ g)
_ = ⊸≡Equiv
```

### Derivatives, Universally

```agda
open import Derivative.Derivative
```

**Definition 3.6**:
The derivative of an untruncated container.
Its shapes contain an _isolated_ position.
```agda
_ : (S : Type) (P : S → Type)
  → ∂ (S ◁ P) ≡ ((s , p) ∈ (Σ[ s ∈ S ] P s °) ◁ (P s ∖° p))
_ = λ S P → refl
```

**TODO**: Description of the [derivative of the container of lists](Derivative.Indexed.List.md#derivative-of-list), \( ((n : ℕ) \lhd [n]) \).
```agda
open import Derivative.Indexed.List using (∂List)
```
??? note
    We define lists as a \( 1 \)-indexed container (introduced [below](#indexed-containers)) to avoid having to define them twice.

**Problem 3.7**:
Extend the derivative to a functor on the wild category of containers and linear morphisms, `ℂont∞`.
```agda
_ : WildFunctor ℂont⊸∞ ℂont⊸∞
_ = ∂∞
```

**Proposition 3.8**:
Taking derivatives preserves the truncation level of containers (except for very low levels).
```agda
_ : ∀ (n k : HLevel)
  → isTruncatedContainer (2 + n) (1 + k) F
  → isTruncatedContainer (2 + n) (1 + k) (∂ F)
_ = isTruncatedDerivative
```

**Corollary 3.9**:
\( \partial \) restricts to an endofunctor of the 1-category of set-truncated containers.
```agda
_ : Functor ℂont⊸ ℂont⊸
_ = ∂ₛ
```

**Problem 3.10**:
Define a wild adjunction \( \_ \otimes \mathsf{Id} \dashv \partial \).
This consists of two families of morphisms `unit` and `counit`,
```agda
open import Derivative.Adjunction

_ : F ⊸ (∂ (F ⊗Id))
_ = unit _

_ : (∂ G ⊗Id) ⊸ G
_ = counit _
```
natural in \( F \) and \( G \), respectively,
```agda
_ = is-natural-unit
_ = is-natural-counit
```
and zig-zag fillers
```agda
_ : [ unit F ]⊗Id ⋆ counit (F ⊗Id) ≡ id (F ⊗Id)
_ = zig≡ _

_ : unit (∂ G) ⋆ ∂[ counit G ] ≡ id (∂ G)
_ = zag≡ _
```

**Theorem 3.11**:
The above restricts to an adjunction in the 1-category of set-truncated containers.
```agda
_ : -⊗Id ⊣ ∂ₛ
_ = -⊗Id⊣∂
```

### Basic Laws of Derivatives

```agda
open import Derivative.Properties
```

**Proposition 3.13**:
Derivative of containers whose positions are propositions.
```agda
_ : (S : Type) {P : S → Type}
  → (∀ s → isProp (P s))
  → Equiv (∂ (S ◁ P)) (Σ S P ◁ const 𝟘)
_ = ∂-prop-trunc
```

**Proposition 3.14**:
The sum- and product rules.
```agda
_ : Equiv (∂ (F ⊕ G)) (∂ F ⊕ ∂ G)
_ = sum-rule _ _

_ : Equiv (∂ (F ⊗ G)) ((∂ F ⊗ G) ⊕ (F ⊗ ∂ G))
_ = prod-rule _ _
```

**Proposition 3.15**:
The `Bag` container is a fixed point of \( \partial \).
```agda
open import Derivative.Bag

_ : Equiv (∂ Bag) Bag
_ = ∂-Bag-equiv
```

**Proposition 3.16**:
Any predicate closed under addition and removal of single points induces a fixed point of \( \partial \).
```agda
module _
  (P : Type → Type)
  (is-prop-P : ∀ A → isProp (P A))
  (is-P-+1 : ∀ {A : Type} → P A → P (A ⊎ 𝟙))
  (is-P-∖ : ∀ {A : Type} → P A → (a : A °) → P (A ∖° a))
  where

  open Derivative.Bag.Universe P is-prop-P is-P-+1 is-P-∖
    renaming (uBag to Bagᴾ)

  _ : Equiv (∂ Bagᴾ) Bagᴾ
  _ = ∂-uBag
```

## The Chain Rule

```agda
open import Derivative.ChainRule
```

**Problem 4.1**:
The lax chain rule.
```agda
_ : (((∂ F) [ G ]) ⊗ ∂ G) ⊸ (∂ (F [ G ]))
_ = chain-rule _ _
```

**Definition 4.2**:
A morphism of containers is an embedding if its shape map is an embedding.
```agda
isContainerEmbedding : F ⊸ G → Type _
isContainerEmbedding = λ f → isEmbedding (shape f)
```

**Proposition 4.3**:
The chain rule is an embedding of containers.
```agda
_ : isContainerEmbedding (chain-rule F G)
_ = isEmbedding-chain-shape-map _ _
```

**Proposition 4.4**:
The chain rule is an equivalence iff `Σ-isolate` is.
```agda
module _ (F G : Container ℓ ℓ) where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  _ : isEquiv (chain-rule F G .shape) ≃ (∀ s → (f : P s → T) → isEquiv (Σ-isolate (P s) (Q ∘ f)))
  _ = isEquivChainRule≃isEquiv-Σ-isolated F G
```

**Theorem 4.5**:
For discrete containers, the chain rule is an equivalence.
Therefore it is an isomorphism in the 1-category of set-truncated containers, `ℂont`.
```agda
_ : (F G : DiscreteContainer ℓ ℓ) → isEquiv (chain-rule (F .fst) (G .fst) .shape)
_ = DiscreteContainer→isStrong
```

**Theorem 4.6**:
The chain rule is invertible for arbitrary containers if and only if arbitrary types are discrete.
This is impossible in the presence of types of higher truncation level.
```agda
_ : ((F G : Container ℓ ℓ) → isEquiv (chain-rule F G .shape)) ≃ ((A : Type ℓ) → Discrete A)
_ = isGloballyStrong≃AllTypesDiscrete

_ : ¬ isGloballyStrong ℓ-zero
_ = ¬isGloballyStrong
```

**Corollary 4.7**:
The chain rule is an equivalence for all set-truncated containers if and only if all sets are discrete.
```agda
_ :
  ((F G : SetContainer ℓ ℓ) → isEquiv (chain-rule (F .fst) (G .fst) .shape))
    ≃
  ((A : hSet ℓ) → Discrete ⟨ A ⟩)
_ = isStrongSets≃AllSetsDiscrete
```

## Derivatives of Fixed Points

### Indexed Containers { #indexed-containers }

```agda
import Derivative.Indexed.Container as Containerᴵ
```

**Definition 5.1**:
Indexed containers have positions indexed by some \( \mathsf{Ix} : \Type \).
```agda
Containerᴵ : (Ix : Type) → Type _
Containerᴵ = Containerᴵ.Container ℓ-zero

_ : Containerᴵ Ix ≃ (Σ[ S ∈ Type ] (Ix → S → Type))
_ = Containerᴵ.Container-Σ-equiv
```

??? note "Overloading notation"
    Unfortunately, Agda does not allow overloading the names of definitions for indexed and non-indexed containers.
    The indexed versions are suffixed with `ᴵ`, if necessary.

```agda
open Containerᴵ
  using (₀ ; ₁ ; 𝟚 ; isContainerEquiv ; _⧟_ ; ↑ ; π₁)
  renaming
    ( _⊗_ to _⊗ᴵ_
    ; _⊕_ to _⊕ᴵ_
    ; _⋆_ to _⋆ᴵ_
    ; _⊸_ to _⊸ᴵ_
    ; isContainerEmbedding to isContainerEmbeddingᴵ
    ; [-]-map to [_]-map
    )
open Containerᴵ.Container
```

**Definition 5.3**:
Substitution for indexed containers.
```agda
_[_]ᴵ : (F : Containerᴵ (Maybe Ix)) (G : Containerᴵ Ix) → Containerᴵ Ix
_[_]ᴵ = Containerᴵ._[_]
```

**Definition 5.4**:
The derivative of an indexed container is defined for each _isolated_ index \( i : \mathsf{Ix}^\circ \).
```agda
import Derivative.Indexed.Derivative as IndexedDerivative

∂ᴵ : (i : Ix °) → (F : Containerᴵ Ix) → Containerᴵ Ix
∂ᴵ = IndexedDerivative.∂
```

Shorthands for the derivative of unary containers (`∂ᴵ tt°`),
and the two derivatives of binary containers.
```agda
open IndexedDerivative using (∂• ; ∂₀ ; ∂₁)
```

**Problem 5.5**:
The chain rule for binary containers.
```agda
open import Derivative.Indexed.ChainRule as IndexedChainRule

_ :
  ∀ (F : Containerᴵ 𝟚)
  → (G : Containerᴵ _)
  → ((∂₀ F [ G ]ᴵ) ⊕ᴵ ((∂₁ F [ G ]ᴵ) ⊗ᴵ ∂• G)) ⊸ᴵ ∂• (F [ G ]ᴵ)
_ = binary-chain-rule
```

**Proposition 5.6**:
The binary chain rule is an embedding.
```agda
_ : (F : Containerᴵ 𝟚) (G : Containerᴵ 𝟙)
  → isContainerEmbeddingᴵ (binary-chain-rule F G)
_ = isContainerEmbeddingChainRule
```

**Proposition 5.7**:
Like for unary containers, the binary chain rule is an equivalence iff `Σ-isolate` is.
```agda
_ : (F : Containerᴵ 𝟚) (G : Containerᴵ 𝟙) →
  isContainerEquiv (binary-chain-rule F G)
    ≃
  (∀ s f → isEquiv (Σ-isolate (F .Pos ₁ s) (G .Pos _ ∘ f)))
_ = isEquivBinaryChainRule≃isEquiv-Σ-isolate
```

**Proposition 5.8**:
For discrete containers, the binary chain rule is an equivalence.
```agda
_ : (F : Containerᴵ 𝟚) (G : Containerᴵ 𝟙)
  → (∀ s → Discrete (Pos F ₁ s))
  → (∀ t → Discrete (Pos G • t))
  → isContainerEquiv (binary-chain-rule F G)
_ = DiscreteContainer→isEquivBinaryChainRule
```

### Fixed Points of Containers

```agda
open import Derivative.Indexed.Mu
```

**Problem 5.9**:
Substitution \( F[\_] \) is a (wild) endofunctor.
```agda
_ : (F : Containerᴵ (Maybe Ix)) {G G′ : Containerᴵ Ix}
  → G ⊸ᴵ G′
  → (F [ G ]ᴵ) ⊸ᴵ (F [ G′ ]ᴵ)
_ = [_]-map

_ = Containerᴵ.[-]-map-id
_ = Containerᴵ.[-]-map-⋆
```

**Problem 5.10**:
\( F[\_] \)-algebras form a wild category.
```agda
```

**Definition 5.12**:
For any \( I+1 \)-indexed container \( F \) there is an \( I \)-indexed fixed point container \( μ F \).
```agda
_ : (F : Containerᴵ (Maybe Ix)) → Containerᴵ Ix
_ = μ
```

**TODO**: Description of [lists as a fixpoint](Derivative.Indexed.List.md#list-as-fixpoint).
```agda
open import Derivative.Indexed.List using (μL⧟List)
```

**Problem 5.13**:
Define an equivalence of containers \( F [ {μ F} ] ⧟ μ F \).
```agda
_ : (F : Containerᴵ (Maybe Ix)) → (F [ μ F ]ᴵ) ⧟ (μ F)
_ = μ-in-equiv
```

**Problem 5.14**:
Derive a recursion principle for fixed-point containers.
```agda
module _
  (F : Containerᴵ (Maybe Ix))
  (G : Containerᴵ Ix)
  (α : F [ G ]ᴵ ⊸ᴵ G)
  where
  _ : μ F ⊸ᴵ G
  _ = μ-rec F G α

  _ : μ-in F ⋆ᴵ μ-rec F G α ≡ [ F ]-map (μ-rec F G α) ⋆ᴵ α
  _ = μ-rec-β F G α
```

**Theorem 5.15**:
Every container admits a smallest fixed point in the wild category of containers.
For any \( F[\_]\)-algebra \( α : F[G] ⊸ G \), there is a unique algebra map \( α^* : μ F ⊸ G \):
```agda
  _ : ∃![ α* ∈ μ F ⊸ᴵ G ] μ-in F ⋆ᴵ α* ≡ [ F ]-map α* ⋆ᴵ α
  _ = μ-rec-unique F G α
```

### The Fixed Point Rule

```agda
open import Derivative.Indexed.MuRule
```

**Problem 5.16**:
The lax \( μ \)-rule.
```agda
_ : (F : Containerᴵ 𝟚)
  → μ (↑ (∂₀ F [ μ F ]ᴵ) ⊕ᴵ (↑ (∂₁ F [ μ F ]ᴵ) ⊗ᴵ π₁)) ⊸ᴵ ∂• (μ F)
_ = μ-rule
```

**Lemma 5.17**:
The μ-recursor reflects equivalences:
```agda
_ : (F : Containerᴵ (Maybe Ix)) (G : Containerᴵ Ix)
  → (φ : (F [ G ]ᴵ) ⊸ᴵ G)
  → isContainerEquiv (μ-rec F G φ)
  → isContainerEquiv φ
_ = isEquivFrom-μ-rec
```

**Proposition 5.18**:
If the \( μ \)-rule is an equivalence, then so is the corresponding chain rule.
```agda
_ : (F : Containerᴵ 𝟚)
  → isContainerEquiv (μ-rule F)
  → isContainerEquiv (binary-chain-rule F (μ F))
_ = StrongFixRule.isEquiv-chain-rule
```

**Lemma 5.19**:
The \( μ \)-recursor preserves embeddings.
```agda
_ : (F : Containerᴵ (Maybe Ix)) (G : Containerᴵ Ix)
  → (φ : (F [ G ]ᴵ) ⊸ᴵ G)
  → isContainerEmbeddingᴵ φ
  → isContainerEmbeddingᴵ (μ-rec F G φ)
_ = isEmbedding-μ-rec
```

**Lemma 5.20**:
The recursor for \( \mathsf{W} \)-types preserves embeddings.
```agda
_ : {S : Type} {P : S → Type} {A : Type}
  → (sup* : (Σ[ s ∈ S ] (P s → A)) → A)
  → isEmbedding sup*
  → isEmbedding (W-rec sup*)
_ = isEmbedding-W-rec
```

**Lemma 5.21**:
The lax \( μ \)-rule is an embedding of containers.
```agda
_ : (F : Containerᴵ 𝟚) → isContainerEmbeddingᴵ (μ-rule F)
_ = isContainerEmbedding-μ-rule
```

**Proposition 5.22**:
If the chain rule is an equivalence, so is the μ-rule.
```agda
_ : (F : Containerᴵ 𝟚)
  → isContainerEquiv (binary-chain-rule F (μ F))
  → isContainerEquiv (μ-rule F)
_ = StrongChainRule.isEquiv-μ-rule
```

**Theorem 5.23**:
The \( μ \)-rule is an equivalence if and only if the corresponding chain rule is.
```agda
_ : (F : Containerᴵ 𝟚)
  → isContainerEquiv (μ-rule F) ≃ isContainerEquiv (binary-chain-rule F (μ F))
_ = isContainerEquiv-μ-rule≃isContainerEquiv-binary-chain-rule
```

Given a tree \( x : \mathsf{W}(S, P) \), the type of \( Q \)-labelled finite paths into \( x \)
is \( \bar{\mathsf{W}}_{S,P,Q}(x) \), written here as
```agda
_ : (S : Type) (P Q : S → Type)
  → W S P → Type
_ = Wᴰ
```

**Lemma 5.24**:
If both branching \( P : S → \mathsf{Type} \) and labeling of nodes \( Q : S → \mathsf{Type} \) are discrete,
then paths into any \( x : \mathsf{W}(S, P) \) are discrete:
```agda
_ : (S : Type) (P Q : S → Type)
  → (∀ s → Discrete (P s))
  → (∀ s → Discrete (Q s))
  → (x : W S P) → Discrete (Wᴰ S P Q x)
_ = discrete-Wᴰ
```

**Lemma 5.25**:
If \( F \) is a discrete container, then so is \( μ F \):
```agda
_ : (F : Containerᴵ 𝟚)
  → (∀ ix s → Discrete (F .Pos ix s))
  → (∀ w → Discrete (μ F .Pos • w))
_ = μ-discrete
```

**Proposition 5.26**:
For discrete containers the \( μ \)-rule is an equivalence.
```agda
_ : (F : Containerᴵ 𝟚) → (∀ ix s → Discrete (F .Pos ix s)) → isContainerEquiv (μ-rule F)
_ = Discrete.isEquiv-μ-rule
```
