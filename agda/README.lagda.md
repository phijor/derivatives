# Overview

This site documents the Agda implementation of the results of [_Derivatives of Containers in Univalent Foundations (arXiv:2512.17484)_](https://arxiv.org/abs/2512.17484).
The overview on this page mirrors the paper.
It lists each numbered result and links it to the corresponding implementation in the library.
Many submodules of this library have additional documentation
which explains proofs and constructions in greater detail than what would have appropriate for the paper.

The library does not depend on additional `postulate`s, nor does it have any open holes.
It is accepted by Agda in `--safe` mode.
```agda
{-# OPTIONS --safe #-}
```

The Agda source code, as well as further documentation, can be found at
<center>
  <a href="https://codeberg.org/phijor/derivatives">codeberg.org/phijor/derivatives</a>
</center>

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
open import Cubical.Categories.Functor.Base hiding (Id)
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

**Lemma 2.11, Proposition 2.12**:
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

**Definition 3.2, 3.3**:
A linear morphism of containers consists of a map of shapes,
and a family of equivalences of positions.
```agda
_ : F ⊸ G ≃ (Σ[ fₛₕ ∈ (F .Shape → G .Shape) ] ∀ s → G .Pos (fₛₕ s) ≃ F .Pos s)
_ = ⊸-Σ-equiv
```

Containers and linear morphisms assemble into a wild category.
Set-truncated containers form a 1-category.
```agda
open import Derivative.Category ℓ-zero

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

**Definition 3.5**:
The extent of a container.
```agda
⟦_⟧ : (F : Container _ _) → Type → Type
⟦ S ◁ P ⟧ X = Σ[ s ∈ S ] (P s → X)
```

**Definition 3.6**
Basic operations on containers.
<!--
```agda
module _ where
```
-->
* Product:
  ```agda
  _ = _⊗_
  ```
* Sum:
  ```agda
  _ = _⊕_
  ```
* Substitution:
  ```agda
  _ = _[_]
  ```
* Constants:
  ```agda
  _ : Type → Container ℓ-zero _
  _ = Const
  ```
* Tuples:
  ```agda
  _ : Type → Container ℓ-zero _
  _ = 𝕪
  ```
* Identity:
  ```agda
  _ : Container ℓ-zero ℓ-zero
  _ = Id
  ```


**Lemma 3.7**:
Extensionality for morphisms says that we can compare them by their shape- and position maps.
```agda
_ : (f g : F ⊸ G)
  → (Σ[ p ∈ f .shape ≡ g .shape ] (PathP (λ i → ∀ s → G .Pos (p i s) ≃ F .Pos s) (f .pos) (g .pos))) ≃ (f ≡ g)
_ = ⊸≡Equiv
```

**Definition 3.8**:
A morphism is an equivalence of containers if its shape map is an equivalence of types.
We bundle this into a record.
```agda
_ : (F G : Container _ _) → Type ℓ-zero
_ = Equiv
```

Equivalences of containers form an identity system.
```agda
open import Derivative.Parametrized.Univalence using (ContainerEquivJ ; containerEquivPreCompEquiv)
```
??? note
    This is defined for parametrized containers (introduced [below](#parametrized-containers)) to avoid having to define it twice.

**Problem 3.9**:
Equivalence-induction for containers.
```agda
_ = ContainerEquivJ
```

**Lemma 3.10**:
Precomposition with a container equivalence is an equivalence of types.
```agda
_ = ContainerEquivJ
```

### Derivatives, Universally

```agda
open import Derivative.Derivative
```

**Definition 3.11**:
The derivative of an untruncated container.
Its shapes contain an _isolated_ position.
```agda
_ : (S : Type) (P : S → Type)
  → ∂ (S ◁ P) ≡ ((s , p) ∈ (Σ[ s ∈ S ] P s °) ◁ (P s ∖° p))
_ = λ S P → refl
```

**Example 3.12**:
Description of the [derivative of the container of lists](Derivative.Examples.List.md#derivative-of-list), \( ((n : ℕ) \lhd [n]) \).
```agda
open import Derivative.Examples.List using (∂List)
```
??? note
    We define lists as a \( 1 \)-parametrized container (introduced [below](#parametrized-containers)) to avoid having to define them twice.

**Problem 3.13**:
Extend the derivative to a functor on the wild category of containers and linear morphisms, `ℂont∞`.
```agda
_ : WildFunctor ℂont⊸∞ ℂont⊸∞
_ = ∂∞
```

**Proposition 3.14**:
Taking derivatives preserves the truncation level of containers (except for very low levels).
```agda
_ : ∀ (n k : HLevel)
  → isTruncatedContainer (2 + n) (1 + k) F
  → isTruncatedContainer (2 + n) (1 + k) (∂ F)
_ = isTruncatedDerivative
```

**Corollary 3.15**:
\( \partial \) restricts to an endofunctor of the 1-category of set-truncated containers.
```agda
_ : Functor ℂont⊸ ℂont⊸
_ = ∂ₛ
```

**Problem 3.16**:
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
These data assemble into a wild adjunction:
```agda
open import Derivative.Basics.WildCategories using (_⊣∞_)

_ : -⊗Id ⊣∞ ∂∞
_ = ⊗Id-∂-wild-adjunction
```

**Theorem 3.17**:
The above restricts to an adjunction in the 1-category of set-truncated containers.
```agda
_ : -⊗Idₛ ⊣ ∂ₛ
_ = ⊗Id-∂-adjunction
```

**Corollary 3.18**:
There is an adjunction \( \_ ⊗ \mathsf{y}[n] ⊣ ∂^n \) in the 1-category
of set-truncated containers and linear morphisms.

We have decided to not formalize this as stated.
This follows directly from composing `⊗Id-∂-adjunction` with itself \( n \) times.
The added overhead of a formal statement is, in our opinion, not worth the marginal gain.

We do, however, prove something much more general which is discussed in the conclusion
of the paper, and [below](#future-work):
It is possible to construct a _wild_ right-adjoint \( ∂^H \) to \( \_ ⊗ \mathsf{y}(H) \),
for an _arbitrary type_ \( H \).
For \( H = [n] \), one can (but we do not) prove that \( ∂^n \) and \( ∂^{[n]} \) are propositionally equal,
hence \( \_ ⊗ \mathsf{y}[n] ⊣ ∂^n \).

### Basic Laws of Derivatives

```agda
open import Derivative.Properties
```

**Proposition 3.19**:
Derivative of containers whose positions are propositions.
```agda
_ : (S : Type) {P : S → Type}
  → (∀ s → isProp (P s))
  → Equiv (∂ (S ◁ P)) (Σ S P ◁ const 𝟘)
_ = ∂-prop-trunc
```

**Proposition 3.20**:
The sum- and product rules.
```agda
_ : Equiv (∂ (F ⊕ G)) (∂ F ⊕ ∂ G)
_ = sum-rule _ _

_ : Equiv (∂ (F ⊗ G)) ((∂ F ⊗ G) ⊕ (F ⊗ ∂ G))
_ = prod-rule _ _
```

**Proposition 3.21**:
The `Bag` container is a fixed point of \( \partial \).
```agda
open import Derivative.Examples.Bag

_ : Equiv (∂ Bag) Bag
_ = ∂-Bag-equiv
```

**Proposition 3.22**:
Any predicate closed under addition and removal of single points induces a fixed point of \( \partial \).
```agda
module _
  (P : Type → Type)
  (is-prop-P : ∀ A → isProp (P A))
  (is-P-+1 : ∀ {A : Type} → P A → P (A ⊎ 𝟙))
  (is-P-∖ : ∀ {A : Type} → P A → (a : A °) → P (A ∖° a))
  where

  open Derivative.Examples.Bag.Universe P is-prop-P is-P-+1 is-P-∖
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
_ : {F G : Container ℓ ℓ} → F ⊸ G → Type _
_ = isContainerEmbedding
```

**Proposition 4.3**:
The chain rule is an embedding of containers.
```agda
_ : isContainerEmbedding (chain-rule F G)
_ = isContainerEmbeddingChainRule _ _
```

**Proposition 4.4**:
The chain rule is an equivalence iff `Σ-isolate` is.
```agda
module _ (F G : Container ℓ ℓ) where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  _ : isContainerEquiv (chain-rule F G) ≃ (∀ s → (f : P s → T) → isEquiv (Σ-isolate (P s) (Q ∘ f)))
  _ = isEquivChainRule≃isEquiv-Σ-isolated F G
```

**Theorem 4.5**:
For discrete containers, the chain rule is an equivalence.
Therefore it is an isomorphism in the 1-category of set-truncated containers, `ℂont`.
```agda
_ : (F G : DiscreteContainer ℓ ℓ) → isStrong (F .fst) (G .fst)
_ = DiscreteContainer→isStrong
```

**Theorem 4.6**:
The chain rule is invertible for arbitrary containers if and only if arbitrary types are discrete.
This is impossible in the presence of types of higher truncation level.
```agda
_ : ((F G : Container ℓ ℓ) → isStrong F G) ≃ ((A : Type ℓ) → Discrete A)
_ = isGloballyStrong≃AllTypesDiscrete

_ : ¬ isGloballyStrong ℓ-zero
_ = ¬isGloballyStrong
```

**Corollary 4.7**:
The chain rule is an equivalence for all set-truncated containers if and only if all sets are discrete.
```agda
_ :
  ((F G : SetContainer ℓ ℓ) → isStrong (F .fst) (G .fst))
    ≃
  ((A : hSet ℓ) → Discrete ⟨ A ⟩)
_ = isStrongSets≃AllSetsDiscrete
```

## Derivatives of Fixed Points

### Parametrized Containers { #parametrized-containers }

```agda
import Derivative.Parametrized.Container as Containerᴾ
```

**Definition 5.1**:
Parametrized containers have positions indexed by some \( \mathsf{Ix} : \mathsf{Type} \).
```agda
Containerᴾ : (Ix : Type) → Type _
Containerᴾ = Containerᴾ.Container ℓ-zero

_ : Containerᴾ Ix ≃ (Σ[ S ∈ Type ] (Ix → S → Type))
_ = Containerᴾ.Container-Σ-equiv
```

??? note "Overloading notation"
    Unfortunately, Agda does not allow overloading the names of definitions for parametrized and unary containers.
    The parametrized versions are suffixed with `ᴾ`, if necessary.

```agda
open Containerᴾ
  using (₀ ; ₁ ; 𝟚 ; _⧟_ ; ↑ ; π₁)
  renaming
    ( _⊗_ to _⊗ᴾ_
    ; _⊕_ to _⊕ᴾ_
    ; _⋆_ to _⋆ᴾ_
    ; _⊸_ to _⊸ᴾ_
    ; isContainerEquiv to isContainerEquivᴾ
    ; isContainerEmbedding to isContainerEmbeddingᴾ
    ; [-]-map to [_]-map
    )
open Containerᴾ.Container
```

**Definition 5.2**:
Substitution for parametrized containers.
```agda
_[_]ᴾ : (F : Containerᴾ (Maybe Ix)) (G : Containerᴾ Ix) → Containerᴾ Ix
_[_]ᴾ = Containerᴾ._[_]
```

**Definition 5.3**:
The derivative of a parametrized container is defined for each _isolated_ index \( i : \mathsf{Ix}^\circ \).
```agda
import Derivative.Parametrized.Derivative as ParametrizedDerivative

∂ᴾ : (i : Ix °) → (F : Containerᴾ Ix) → Containerᴾ Ix
∂ᴾ = ParametrizedDerivative.∂
```

Shorthands for the derivative of unary containers (`∂ᴾ tt°`),
and the two derivatives of binary containers.
```agda
open ParametrizedDerivative using (∂• ; ∂₀ ; ∂₁)
```

**Problem 5.4**:
The chain rule for binary containers.
```agda
open import Derivative.Parametrized.ChainRule as ParametrizedChainRule
  renaming (isContainerEmbeddingChainRule to isContainerEmbeddingChainRuleᴾ)

_ :
  ∀ (F : Containerᴾ 𝟚)
  → (G : Containerᴾ _)
  → ((∂₀ F [ G ]ᴾ) ⊕ᴾ ((∂₁ F [ G ]ᴾ) ⊗ᴾ ∂• G)) ⊸ᴾ ∂• (F [ G ]ᴾ)
_ = binary-chain-rule
```

**Proposition 5.5**:
The binary chain rule is an embedding.
```agda
_ : (F : Containerᴾ 𝟚) (G : Containerᴾ 𝟙)
  → isContainerEmbeddingᴾ (binary-chain-rule F G)
_ = isContainerEmbeddingChainRuleᴾ
```

**Proposition 5.6**:
Like for unary containers, the binary chain rule is an equivalence iff `Σ-isolate` is.
```agda
_ : (F : Containerᴾ 𝟚) (G : Containerᴾ 𝟙) →
  isContainerEquivᴾ (binary-chain-rule F G)
    ≃
  (∀ s f → isEquiv (Σ-isolate (F .Pos ₁ s) (G .Pos _ ∘ f)))
_ = isEquivBinaryChainRule≃isEquiv-Σ-isolate
```

**Proposition 5.7**:
For discrete containers, the binary chain rule is an equivalence.
```agda
_ : (F : Containerᴾ 𝟚) (G : Containerᴾ 𝟙)
  → (∀ s → Discrete (Pos F ₁ s))
  → (∀ t → Discrete (Pos G • t))
  → isContainerEquivᴾ (binary-chain-rule F G)
_ = DiscreteContainer→isEquivBinaryChainRule
```

### Fixed Points of Containers

```agda
open import Derivative.Parametrized.Mu
```

**Problem 5.8**:
Substitution \( F[\_] \) is a (wild) endofunctor.
```agda
_ : (F : Containerᴾ (Maybe Ix)) {G G′ : Containerᴾ Ix}
  → G ⊸ᴾ G′
  → (F [ G ]ᴾ) ⊸ᴾ (F [ G′ ]ᴾ)
_ = [_]-map

_ = Containerᴾ.[-]-map-id
_ = Containerᴾ.[-]-map-⋆
```

**Problem 5.9**:
\( F[\_] \)-algebras form a wild category.
```agda
private module _ (F : Containerᴾ (Maybe Ix)) where
  Alg : Type _
  Alg = Σ[ X ∈ Containerᴾ Ix ] (F [ X ]ᴾ ⊸ᴾ X)

  AlgHom : Alg → Alg → Type _
  AlgHom (X , f) (Y , g) = Σ[ h ∈ X ⊸ᴾ Y ] f ⋆ᴾ h ≡ [ F ]-map h ⋆ᴾ g
```
??? note
    We chose to omit the proof that \( F[\_] \)-algebras form a wild category from the formalization.
    Defining the necessary coherence between commutative squares is challenging for technical reasons;
    a formal proof only obscures the intuition that \( F[\_] \) acts coherently also on homotopies of container morphisms.
    At the same time, no further construction depends on these coherences.

**Definition 5.10**:
A (least) container fixpoint is an initial \( F[\_] \)-algebra.
```agda
  isLeastFixpoint : (μ : Alg) → Type _
  isLeastFixpoint μ = ∀ h → isContr (AlgHom μ h)
```

**Definition 5.11**:
For any \( I+1 \)-parametrized container \( F \) there is an \( I \)-parametrized fixed point container \( μ F \).
```agda
_ : (F : Containerᴾ (Maybe Ix)) → Containerᴾ Ix
_ = μ
```

**Example 5.12**:
Lists can be described [as a fixpoint](Derivative.Examples.List.md#list-as-fixpoint).
```agda
open import Derivative.Examples.List using (μL⧟List)
```

**Problem 5.13**:
Define an equivalence of containers \( F [ {μ F} ] ⧟ μ F \).
```agda
_ : (F : Containerᴾ (Maybe Ix)) → (F [ μ F ]ᴾ) ⧟ (μ F)
_ = μ-in-equiv
```

**Problem 5.14**:
Derive a recursion principle for fixed-point containers.
```agda
module _
  (F : Containerᴾ (Maybe Ix))
  (G : Containerᴾ Ix)
  (α : F [ G ]ᴾ ⊸ᴾ G)
  where
  _ : μ F ⊸ᴾ G
  _ = μ-rec F G α

  _ : μ-in F ⋆ᴾ μ-rec F G α ≡ [ F ]-map (μ-rec F G α) ⋆ᴾ α
  _ = μ-rec-β F G α
```

**Proposition 5.15**:
The recursion principle for containers is unique as a coalgebra-to-algebra morphism.
```agda
  _ : ∃![ α* ∈ μ F ⊸ᴾ G ] α* ≡ μ-out F ⋆ᴾ [ F ]-map α* ⋆ᴾ α
  _ = μ-rec-coalgebra-to-algebra.unique F G α
```

**Theorem 5.16**:
Every container admits a least fixed point in the wild category of containers.
For any \( F[\_]\)-algebra \( α : F[G] ⊸ G \), there is a unique algebra map \( α^* : μ F ⊸ G \):
```agda
  _ : ∃![ α* ∈ μ F ⊸ᴾ G ] μ-in F ⋆ᴾ α* ≡ [ F ]-map α* ⋆ᴾ α
  _ = μ-rec-unique F G α

_ : (F : Containerᴾ (Maybe Ix)) → isLeastFixpoint F (μ F , μ-in F)
_ = uncurry ∘ μ-rec-unique
```

### The Fixed Point Rule

```agda
open import Derivative.Parametrized.MuRule
```

**Problem 5.17**:
The lax \( μ \)-rule.
```agda
_ : (F : Containerᴾ 𝟚)
  → μ (↑ (∂₀ F [ μ F ]ᴾ) ⊕ᴾ (↑ (∂₁ F [ μ F ]ᴾ) ⊗ᴾ π₁)) ⊸ᴾ ∂• (μ F)
_ = μ-rule
```

**Lemma 5.18**:
The μ-recursor reflects equivalences:
```agda
_ : (F : Containerᴾ (Maybe Ix)) (G : Containerᴾ Ix)
  → (φ : (F [ G ]ᴾ) ⊸ᴾ G)
  → isContainerEquivᴾ (μ-rec F G φ)
  → isContainerEquivᴾ φ
_ = isEquivFrom-μ-rec
```

**Proposition 5.19**:
If the \( μ \)-rule is an equivalence, then so is the corresponding chain rule.
```agda
_ : (F : Containerᴾ 𝟚)
  → isContainerEquivᴾ (μ-rule F)
  → isContainerEquivᴾ (binary-chain-rule F (μ F))
_ = StrongFixRule.isEquiv-chain-rule
```

**Lemma 5.20**:
The \( μ \)-recursor preserves embeddings.
```agda
_ : (F : Containerᴾ (Maybe Ix)) (G : Containerᴾ Ix)
  → (φ : (F [ G ]ᴾ) ⊸ᴾ G)
  → isContainerEmbeddingᴾ φ
  → isContainerEmbeddingᴾ (μ-rec F G φ)
_ = isEmbedding-μ-rec
```

**Problem 5.21**:
If the algebra \( \mathsf{sup}^* \) is an embedding,
the fibers of the \( \mathsf{W} \)-recursor over its own image can be characterized recursively:
a fiber over a node is the product of the fibers over its children.
```agda
_ : {S : Type} {P : S → Type} {A : Type}
  → (sup* : (Σ[ s ∈ S ] (P s → A)) → A)
  → isEmbedding sup*
  → (s : S) (f : P s → W S P)
  → fiber (W-rec sup*) (W-rec sup* (sup s f))
    ≃ ((p : P s) → fiber (W-rec sup*) (W-rec sup* (f p)))
_ = isEmbedding→W-rec-fiber-equiv
```

**Lemma 5.22**:
The recursor for \( \mathsf{W} \)-types preserves embeddings.
```agda
_ : {S : Type} {P : S → Type} {A : Type}
  → (sup* : (Σ[ s ∈ S ] (P s → A)) → A)
  → isEmbedding sup*
  → isEmbedding (W-rec sup*)
_ = isEmbedding-W-rec
```

**Lemma 5.23**:
The lax \( μ \)-rule is an embedding of containers.
```agda
_ : (F : Containerᴾ 𝟚) → isContainerEmbeddingᴾ (μ-rule F)
_ = isContainerEmbedding-μ-rule
```

**Proposition 5.24**:
If the chain rule is an equivalence, so is the μ-rule.
```agda
_ : (F : Containerᴾ 𝟚)
  → isContainerEquivᴾ (binary-chain-rule F (μ F))
  → isContainerEquivᴾ (μ-rule F)
_ = StrongChainRule.isEquiv-μ-rule
```

**Theorem 5.25**:
The \( μ \)-rule is an equivalence if and only if the corresponding chain rule is.
```agda
_ : (F : Containerᴾ 𝟚)
  → isContainerEquivᴾ (μ-rule F) ≃ isContainerEquivᴾ (binary-chain-rule F (μ F))
_ = isContainerEquiv-μ-rule≃isContainerEquiv-binary-chain-rule
```

Given a tree \( x : \mathsf{W}(S, P) \), the type of \( Q \)-labelled finite paths into \( x \)
is \( \bar{\mathsf{W}}_{S,P,Q}(x) \), written here as
```agda
_ : (S : Type) (P Q : S → Type)
  → W S P → Type
_ = Wᴰ
```

**Lemma 5.26**:
If both branching \( P : S → \mathsf{Type} \) and labeling of nodes \( Q : S → \mathsf{Type} \) are discrete,
then paths into any \( x : \mathsf{W}(S, P) \) are discrete:
```agda
_ : (S : Type) (P Q : S → Type)
  → (∀ s → Discrete (P s))
  → (∀ s → Discrete (Q s))
  → (x : W S P) → Discrete (Wᴰ S P Q x)
_ = discrete-Wᴰ
```

**Lemma 5.27**:
If \( F \) is a discrete container, then so is \( μ F \):
```agda
_ : (F : Containerᴾ 𝟚)
  → (∀ ix s → Discrete (F .Pos ix s))
  → (∀ w → Discrete (μ F .Pos • w))
_ = μ-discrete
```

**Proposition 5.28**:
For discrete containers the \( μ \)-rule is an equivalence.
```agda
_ : (F : Containerᴾ 𝟚) → (∀ ix s → Discrete (F .Pos ix s)) → isContainerEquivᴾ (μ-rule F)
_ = Discrete.isEquiv-μ-rule
```

## Future work { #future-work }

In the conclusion of the paper, we conjecture that \( \_ ⊗ \mathsf{y}(H) \)
has a (wild) right-adjoint for arbitrary types \( H \).
This is indeed the case.
We decided not to include this fact in the main body of the paper in order not to make it longer than it needs to be.

We define a notion of _higher derivative_ relative to some type \( H \) of holes.
```agda
import Derivative.Relative as Rel
```
Instead of considering isolated positions,
we notice that isolated points are exactly _decidable_ embeddings of *the* point \( 1 \):
```agda
open import Derivative.Basics.DecidableEmbedding
  as DecEmb
  using (_↪°_ ; isDecEmbedding ; Isolated≃DecEmbUnit ; _-_)

_ : A ° ≃ (𝟙 ↪° A)
_ = Isolated≃DecEmbUnit
```

This yields a notion of a derivative operation \( ∂^H \) that captures the intuition of "context with a \( H \)-shaped hole":
Shapes of \( ∂^H(S \lhd P) \) are a shape \( s : S \) together with a decidable embedding \( H ↪° P_s \):
```agda
_ : (H : Type) (S : Type) (P : S → Type)
  → Shape (Rel.∂ H (S ◁ P)) ≡ (Σ[ s ∈ S ] (H ↪° P s))
_ = λ H S P → refl
```

For \( H = 1 \), this corresponds exactly to the ordinary ("first") derivative:
```agda
_ : (F : Container ℓ-zero ℓ-zero) → Equiv (∂ F) (Rel.∂ 𝟙 F)
_ = Rel.firstDerivativeEquiv
```

The proof that \( ∂^H \) is right-adjoint to \( \_ ⊗ 𝕪(H) \) is largely like that of Problem 3.16 above.
An isolated point splits a type into two disconnected components:
if \( a : A \) is isolated, then \( A \simeq (A ∖ a) + 1 \).
Similarly, if \( H \) embeds _decidably_ into \( A \), then it splits \( A \) into two components
— the image of \( h \) and its complement.
```agda
_ : {H : Type} → (h : H → A) → DecEmb.isDecEmbedding h → (A - h) ⊎ H ≃ A
_ = curry DecEmb.remove-sum-left-equiv

_ : A ≃ (A ⊎ B) - inr
_ = DecEmb.sum-inr-remove-equiv
```

This lets us construct a wild adjunction following essentially the same argument as before:
```agda
module _ (H : Type) (F G : Container ℓ-zero ℓ-zero) where
  open Rel using () renaming (∂[_] to ∂-map)

  _ : F ⊸ Rel.∂ H (F ⊗ 𝕪 H)
  _ = Rel.unit H F

  _ : (Rel.∂ H G ⊗ 𝕪 H) ⊸ G
  _ = Rel.counit H G

  _ = Rel.is-natural-unit H
  _ = Rel.is-natural-counit H

  _ : ([ Rel.unit H F ]⊗ (𝕪 H)) ⋆ Rel.counit H (F ⊗ 𝕪 H) ≡ id (F ⊗ 𝕪 H)
  _ = Rel.zig≡ H F

  _ : Rel.unit H (Rel.∂ H G) ⋆ ∂-map H (Rel.counit H G) ≡ id (Rel.∂ H G)
  _ = Rel.zag≡ H G
```
