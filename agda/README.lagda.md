# Overview

```agda
{-# OPTIONS --safe #-}
```

<!--
```agda
module README where

open import Derivative.Prelude hiding (∂ᴵ)
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
The constructors `inl : A → A ⊎ B` and `inr : B → A ⊎ B` preserve and reflect isolated points.
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

The type `A ⊎ 𝟙` is used so often that we abbreviate it as `Maybe A`:
```agda
_ : (A : Type) → Maybe A ≡ (A ⊎ 𝟙)
_ = λ A → refl
```

The point `nothing : Maybe A` is always isolated:
```agda
_ : isIsolated {A = Maybe A} nothing
_ = isIsolatedNothing

_ : (Maybe A) °
_ = nothing°
```

**Problem 2.8**:
The isolated points of `Maybe A` are those of `A` or `nothing`:
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
  _ : (Σ[ a° ∈ A ° ] (B (a° .fst)) °) → (Σ[ a ∈ A ] B a) °
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
`Σ-isolate` is a surjection (hence equivalence) iff pairing `(_,_)` reflects isolated points.
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
Over a fixed *isolated* point `a : A`, pairing `λ b → (a , b)` preserves and reflects isolated points.
```agda
  _ : {a₀ : A} → isIsolated a₀ → (b₀ : B a₀) → isIsolated b₀ ≃ isIsolated {A = Σ A B} (a₀ , b₀)
  _ = isIsolatedFst→isIsolatedSnd≃isIsolatedPair
```

**Proposition 2.16**:
Discreteness of a type can be characterized by `Σ-isolate` at the family `B(a) ≔ (a₀ ≡ a)`.
```agda
_ : Discrete A ≃ ((a₀ : A) → isEquiv (Σ-isolate A (a₀ ≡_)))
_ = Discrete≃isEquiv-Σ-isolate-singl
```

### Removing points
```agda
open import Derivative.Remove
```

The type `A ∖ a₀` is the subtype of "`A` with `a₀` removed".
```agda
_ : (A : Type) → (a₀ : A) → (A ∖ a₀) ≡ (Σ[ a ∈ A ] a₀ ≢ a)
_ = λ A a → refl
```

**Problem 2.17**:
Show that first adding a point to `A`, then removing it gives a type equivalent to `A`.
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

The other way around there is a map that takes `(A ∖ a₀) ⊎ 𝟙` and replaces `nothing` with `a₀`:
```agda
_ : (a₀ : A) → Maybe (A ∖ a₀) → A
_ = replace
```

**Proposition 2.19**:
The map `replace a₀` is an equivalence if and only if `a₀` is isolated.
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
If `a₀` is *h-isolated* (i.e. `isProp (a₀ ≡ a₀)`), then there is a map that
looks like it characterizes removal of points from `Σ`-types.
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
For all `a : A °`, *grafting* extends the domain a function `f : A ∖ a₀ → B` to all of `A`, given some `b₀ : B`.
```agda
_ : (a° : A °) → (((A ∖° a°) → B) × B) → (A → B)
_ = graft
```

**Problem 2.23**:
This defines an *induction-like* principle for maps out of types `A` pointed by an isolated `a₀ : A °`.
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
    Since `transport refl` does not definitionially reduce to the identity function,
    we would have to manually get rid of it everywhere.

## Derivatives of Containers

```agda
open import Derivative.Container
```

**Definition 3.1**:
A container `(S ◁ P)` consists of shapes `S : Type` and over this a family of positions `P : S → Type`.
```agda
_ : (ℓ : Level) → Type (ℓ-suc ℓ)
_ = λ ℓ → Container ℓ ℓ

_ : (S : Type) → (P : S → Type) → Container _ _
_ = λ S P → (S ◁ P)
```

??? note "Universe polymorphism"
    Containers are defined for shapes and positions in any universe.
    For most constructions, we consider containers at a fixed level `ℓ`,
    that is the type `Container ℓ ℓ`.
    Some examples consider containers with large shapes (i.e. `Container (ℓ-suc ℓ) ℓ`), but this is mostly for convenience.
    The shapes of those containers could be resized to a type at level `ℓ`.

<!--
```agda
open Container
open Cart
private
  variable
    F G : Container ℓ-zero ℓ-zero
```
-->

**Definition 3.2**:
A (cartesian) morphism of containers consists of a map of shapes,
and a family of equivalences of positions.
```agda
_ : Cart F G ≃ (Σ[ fₛₕ ∈ (F .Shape → G .Shape) ] ∀ s → G .Pos (fₛₕ s) ≃ F .Pos s)
_ = Cart-Σ-equiv
```

**Definition 3.3**:
A morphism is an equivalence of containers if its shape map is an equivalence of types.
We bundle this into a record.
```agda
_ : (F G : Container _ _) → Type ℓ-zero
_ = Equiv
```

Containers and cartesian morphism assemble into a wild category.
Set-truncated containers form a 1-category.
```agda
open import Derivative.Category ℓ-zero

_ : WildCat _ _
_ = ℂont∞

_ : Category _ _
_ = ℂont
```

**Definition 3.4**:
An `(n, k)`-truncated container has `n`-truncated shapes, and `k`-truncated positions.
```agda
_ : (n k : HLevel) → (F : Container _ _) → Type _
_ = isTruncatedContainer {ℓS = ℓ-zero} {ℓP = ℓ-zero}
```

**Lemma 3.5**:
Extensionality for morphisms says that we can compare them by their shape- and position maps.
```agda
_ : (f g : Cart F G)
  → (Σ[ p ∈ f .shape ≡ g .shape ] (PathP (λ i → ∀ s → G .Pos (p i s) ≃ F .Pos s) (f .pos) (g .pos))) ≃ (f ≡ g)
_ = Cart≡Equiv
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
  → ∂ (S ◁ P) ≡ ((Σ[ s ∈ S ] P s °) ◁ λ (s , p) → (P s ∖° p))
_ = λ S P → refl
```

**Problem 3.7**:
Extend the derivative to a wild functor on `ℂont∞`.
```agda
_ : WildFunctor ℂont∞ ℂont∞
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
`∂` restricts to an endofunctor of the 1-category of set-truncated containers.
```agda
_ : Functor ℂont ℂont
_ = ∂ₛ
```

**Problem 3.10**:
Define a wild adjunction `_⊗ Id ⊣ ∂`.
This consists of two families of morphisms `unit` and `counit`,
```agda
open import Derivative.Adjunction

_ : Cart F (∂ (F ⊗Id))
_ = unit _

_ : Cart (∂ G ⊗Id) G
_ = counit _
```
natural in `F` and `G`, respectively,
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
In the 1-category of set-truncated containers, `_⊗ Id ⊣ ∂ₛ`.
```agda
_ : -⊗Id ⊣ ∂ₛ
_ = -⊗Id⊣∂
```
natural in `F` and `G`, respectively,
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
The `Bag` container is a fixed point of `∂`.
```agda
open import Derivative.Bag

_ : Equiv (∂ Bag) Bag
_ = ∂-Bag-equiv
```

**Proposition 3.16**:
Any predicate closed under addition and removal of single points induces a fixed point of `∂`.
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
_ : Cart (((∂ F) [ G ]) ⊗ ∂ G) (∂ (F [ G ]))
_ = chain-rule _ _
```

**Definition 4.2**:
A morphism of containers is an embedding if its shape map is an embedding.
```agda
isContainerEmbedding : Cart F G → Type _
isContainerEmbedding = λ f → isEmbedding (Cart.shape f)
```

**Proposition 4.3**:
Then chain rule is an embedding of containers.
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
_ = DiscreteContainer→isEquivChainMap
```

**Theorem 4.6**:
If the chain rule is invertible for arbitrary containers if and only if arbitrary types are discrete.
This is impossible in the presence of types of higher truncation level.
```agda
_ : ((F G : Container ℓ ℓ) → isEquiv (chain-rule F G .shape)) ≃ ((A : Type ℓ) → Discrete A)
_ = isEquivChainMap≃AllTypesDiscrete

_ : ¬ hasChainEquiv ℓ-zero
_ = ¬hasChainEquiv
```

**Corollary 4.7**:
The chain rule is an equivalence for all set-truncated containers if and only if all sets are discrete.
```agda
_ :
  ((F G : SetContainer ℓ ℓ) → isEquiv (chain-rule (F .fst) (G .fst) .shape))
    ≃
  ((A : hSet ℓ) → Discrete ⟨ A ⟩)
_ = isEquivChainMapSets≃AllSetsDiscrete
```

## Derivatives of Fixed Points

### Indexed Containers

```agda
import Derivative.Indexed.Container as Containerᴵ
```

**Definition 5.1**:
Indexed containers have positions indexed by some `Ix : Type`.
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
  using (₀ ; ₁ ; 𝟚 ; _⊸_ ; isContainerEquiv ; _⧟_ ; ↑ ; π₁)
  renaming
    ( _⊗_ to _⊗ᴵ_
    ; _⊕_ to _⊕ᴵ_
    ; _⋆_ to _⋆ᴵ_
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
The derivative of an indexed container is defined for each _isolated_ index `i : Ix °`.
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
  → ((∂₀ F [ G ]ᴵ) ⊕ᴵ ((∂₁ F [ G ]ᴵ) ⊗ᴵ ∂• G)) ⊸ ∂• (F [ G ]ᴵ)
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
Substitution `F[_]` is an endofunctor.
```agda
```

**Problem 5.10**:
`F[_]`-algebras form a wild category.
```agda
```

**Definition 5.12**:
For any `I+1`-indexed container `F` there is an `I`-indexed fixed point container `μ F`.
```agda
_ : (F : Containerᴵ (Maybe Ix)) → Containerᴵ Ix
_ = μ
```

**Problem 5.13**:
Define an equivalence of containers `F [ μ F ] ⧟ μ F`.
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
  (α : F [ G ]ᴵ ⊸ G)
  where
  _ : μ F ⊸ G
  _ = μ-rec F G α

  _ : μ-in F ⋆ᴵ μ-rec F G α ≡ [ F ]-map (μ-rec F G α) ⋆ᴵ α
  _ = μ-rec-β F G α
```

**Theorem 5.15**:
Every signature container admits a smallest fixed point in the wild category of containers.
For any `F[_]`-algebra `(G, α)`, there is a unique algebra map `α* : μ F ⊸ G`:
```agda
  _ : ∃![ α* ∈ μ F ⊸ G ] μ-in F ⋆ᴵ α* ≡ [ F ]-map α* ⋆ᴵ α
  _ = μ-rec-unique F G α
```

### The Fixed Point Rule

```agda
open import Derivative.Indexed.MuRule
```

**Problem 5.16**:
The lax μ-rule.
```agda
_ : (F : Containerᴵ 𝟚)
  → μ (↑ (∂₀ F [ μ F ]ᴵ) ⊕ᴵ (↑ (∂₁ F [ μ F ]ᴵ) ⊗ᴵ π₁)) ⊸ ∂• (μ F)
_ = μ-rule
```

**Lemma 5.17**:
The μ-recursor reflects equivalences:
```agda
_ : (F : Containerᴵ (Maybe Ix)) (G : Containerᴵ Ix)
  → (φ : (F [ G ]ᴵ) ⊸ G)
  → isContainerEquiv (μ-rec F G φ)
  → isContainerEquiv φ
_ = isEquivFrom-μ-rec
```

**Proposition 5.18**:
If the μ-rule is an equivalence, then so is the corresponding chain rule.
```agda
_ : (F : Containerᴵ 𝟚)
  → isContainerEquiv (μ-rule F)
  → isContainerEquiv (binary-chain-rule F (μ F))
_ = isEquiv-μ-rule.isEquiv-chain-rule
```

**Lemma 5.19**:
The μ-recursor preserves embeddings.
```agda
_ : (F : Containerᴵ (Maybe Ix)) (G : Containerᴵ Ix)
  → (φ : (F [ G ]ᴵ) ⊸ G)
  → isContainerEmbeddingᴵ φ
  → isContainerEmbeddingᴵ (μ-rec F G φ)
_ = isEmbedding-μ-rec
```

**Lemma 5.20**:
The recursor for `W`-types preserves embeddings.
```agda
_ : {S : Type} {P : S → Type} {A : Type}
  → (sup* : (Σ[ s ∈ S ] (P s → A)) → A)
  → isEmbedding sup*
  → isEmbedding (W-rec sup*)
_ = isEmbedding-W-rec
```

**Lemma 5.21**:
The lax μ-rule is an embedding of containers.
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
_ = isEquiv-μ-rule
```

**Theorem 5.23**:
The μ-rule is an equivalence if and only if the corresponding chain rule is.
```agda
_ : (F : Containerᴵ 𝟚)
  → isContainerEquiv (μ-rule F) ≃ isContainerEquiv (binary-chain-rule F (μ F))
_ = isContainerEquiv-μ-rule≃isContainerEquiv-binary-chain-rule
```

**Lemma 5.25**:
The family `Wᴰ` preserves discreteness:
```agda
_ : (S : Type) (P Q : S → Type)
  → (∀ s → Discrete (P s))
  → (∀ s → Discrete (Q s))
  → (w : W S P) → Discrete (Wᴰ S P Q w)
_ = discrete-Wᴰ
```

**Proposition 5.26**:
For discrete containers the μ-rule is an equivalence.
```agda
_ : (F : Containerᴵ 𝟚) → (∀ ix s → Discrete (F .Pos ix s)) → isContainerEquiv (binary-chain-rule F (μ F))
_ = Discrete→isEquiv-μ-chain-rule
```
