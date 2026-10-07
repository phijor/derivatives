## Containers

<!--
```agda
{-# OPTIONS --safe #-}
module Derivative.Container where

open import Derivative.Prelude
import      Derivative.Basics.Decidable as Dec
open import Derivative.Basics.Embedding using (isEmbedding ; isEquiv→isEmbedding)
import      Derivative.Basics.Maybe as Maybe
open import Derivative.Basics.Sum as Sum using (_⊎_)

open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma.Base

private
  variable
    ℓS ℓP ℓ : Level
```
-->

A container consists of a type `S` of _shapes_ and a family `P : S → Type` of _positions_.
```agda
record Container (ℓS ℓP : Level) : Type (ℓ-suc (ℓ-max ℓS ℓP)) where
  constructor _◁_
  field
    Shape : Type ℓS
    Pos : Shape → Type ℓP
```

<!--
```agda
Container-syntax : (S : Type ℓS) → (P : S → Type ℓP) → Container ℓS ℓP
Container-syntax = _◁_

open Container
```
-->

We denote a container either by \( (S \lhd P) \) or \( (s : S \lhd P(s)) \).
```agda
syntax Container-syntax S (λ s → P) = s ∈ S ◁ P
```

### Truncated and discrete containers

We say that a container is \( (n, k) \)-_truncated_ if we know that its shapes and positions are
\( n \)- and \( k \)-truncated types, respectively.
```agda
isTruncatedContainer : (n k : HLevel) → Container ℓS ℓP → Type _
isTruncatedContainer n k (S ◁ P) = isOfHLevel n S × ∀ s → isOfHLevel k (P s)

TruncatedContainer : (n k : HLevel) (ℓS ℓP : Level) → Type (ℓ-suc (ℓ-max ℓS ℓP))
TruncatedContainer n k ℓS ℓP = Σ (Container ℓS ℓP) (isTruncatedContainer n k)
```

A container is _set-truncated_ or a _set-container_ if its shapes and positions are \( h \)-sets.
```agda
isSetContainer : Container ℓS ℓP → Type _
isSetContainer = isTruncatedContainer h-set h-set

SetContainer : (ℓS ℓP : Level) → Type (ℓ-suc (ℓ-max ℓS ℓP))
SetContainer = TruncatedContainer h-set h-set
```

A container is _discrete_ if its positions are discrete, i.e. have decidable equality.
```agda
isDiscreteContainer : Container ℓS ℓP → Type _
isDiscreteContainer F = ∀ s → Dec.Discrete (F .Pos s)

DiscreteContainer : (ℓS ℓP : Level) → Type _
DiscreteContainer ℓS ℓP = Σ[ F ∈ Container ℓS ℓP ] isDiscreteContainer F
```

### Operations

We denote by `_⊗_` and `_⊕_` the product and sum of containers.
```agda
_⊗_ : (F G : Container ℓS ℓP) → Container _ _
(F ⊗ G) .Shape = F .Shape × G .Shape
(F ⊗ G) .Pos x = F .Pos (x .fst) ⊎ G .Pos (x .snd)
infix 11 _⊗_

_⊕_ : (F G : Container ℓS ℓP) → Container _ _
(F ⊕ G) .Shape = F .Shape ⊎ G .Shape
(F ⊕ G) .Pos (Sum.inl s) = F .Pos s
(F ⊕ G) .Pos (Sum.inr t) = G .Pos t
infix 10 _⊕_
```

For any \( A : \mathsf{Type} \), we define the _tuple_ container \( \mathsf{y}(A) ≔ (1 \lhd A) \):
```agda
𝕪 : (A : Type ℓP) → Container ℓS ℓP
𝕪 A .Shape = 𝟙*
𝕪 A .Pos = const A
```
Its extent \( 〚 \mathsf{y}(A) 〛 \) is the representable functor \( X ↦ X^A \).

The _identity container_ is \( \mathsf{Id} ≔ \mathsf{y}(1) \); its extent is the identity functor.
```agda
Id : Container ℓS ℓP
Id = 𝕪 𝟙*
```

Similarly, there is a _constant_ container \( (S \lhd 0) \) for any \( S : \mathsf{Type} \).
```agda
Const : (S : Type ℓ) → Container ℓ ℓ
Const S .Shape = S
Const S .Pos _ = 𝟘*

One : (ℓ : Level) → Container ℓ ℓ
One ℓ = Const 𝟙*
```

The substitution \( F[G] \) represents the composite data type obtained from substituting \( G \) into the positions of \( F \):
```agda
_[_] : (F G : Container ℓ ℓ) → Container ℓ ℓ
(F [ G ]) .Shape = Σ[ s ∈ F .Shape ] (F .Pos s → G .Shape)
(F [ G ]) .Pos (s , f) = Σ[ p ∈ F .Pos s ] G .Pos (f p)
```

### Linear morphisms

A _linear morphism_ of containers consists of a map of shapes, and a family of equivalences of positions:
```agda
record _⊸_ {ℓS ℓT ℓP ℓQ} (F : Container ℓS ℓP) (G : Container ℓT ℓQ) : Type (ℓ-max (ℓ-max ℓS ℓP) (ℓ-max ℓT ℓQ)) where
  constructor [_◁_]
  field
    shape : F .Shape → G .Shape
    pos : ∀ s → G .Pos (shape s) ≃ F .Pos s

infix 20 _⊸_

open _⊸_
```

We define morphisms as a `record`-type, but sometimes it is useful to view them as a \( Σ \)-type:
```agda
unquoteDecl ⊸-Σ-Iso = declareRecordIsoΣ ⊸-Σ-Iso (quote _⊸_)

⊸-Σ-equiv : ∀ {ℓS ℓT ℓP ℓQ} {F : Container ℓS ℓP} {G : Container ℓT ℓQ}
  → F ⊸ G ≃ (Σ[ fₛₕ ∈ (F .Shape → G .Shape) ] ∀ s → G .Pos (fₛₕ s) ≃ F .Pos s)
⊸-Σ-equiv = isoToEquiv ⊸-Σ-Iso
```

Container morphisms are (extensionally) equal if their maps on shapes and positions agree:
```agda
⊸≡ : {F G : Container ℓS ℓP}
  → {f g : F ⊸ G}
  → (p : f .shape ≡ g .shape)
  → (q : PathP (λ i → ∀ s → G .Pos (p i s) ≃ F .Pos s) (f .pos) (g .pos))
  → f ≡ g
⊸≡ p q i .shape = p i
⊸≡ p q i .pos = q i

⊸≡Equiv : {F G : Container ℓS ℓP}
  → (f g : F ⊸ G)
  → (Σ[ p ∈ f .shape ≡ g .shape ] (PathP (λ i → ∀ s → G .Pos (p i s) ≃ F .Pos s) (f .pos) (g .pos))) ≃ (f ≡ g)
⊸≡Equiv f g = strictIsoToEquiv iso module ⊸≡Equiv where
  iso : Iso _ _
  iso .Iso.fun = uncurry ⊸≡
  iso .Iso.inv p .fst = cong shape p
  iso .Iso.inv p .snd = cong pos p
  iso .Iso.rightInv _ = refl
  iso .Iso.leftInv _ = refl
```

### Composition

Linear morphisms compose, and there is an identity morphism for each container.
```agda
_⋆_ : ∀ {F G H : Container ℓS ℓP} → F ⊸ G → G ⊸ H → F ⊸ H
(f ⋆ g) .shape = g .shape ∘ f .shape
(f ⋆ g) .pos s = g .pos (f .shape s) ∙ₑ f .pos s

id : (F : Container ℓS ℓP) → F ⊸ F
id F .shape s = s
id F .pos s = idEquiv _
```

This defines the structure of a (wild) category,
which we assemble in [`Derivative.Category`](Derivative.Category.html).

We define some notation that lets us compose chains of morphisms:
```agda
module ⊸Reasoning where
  private
    variable
      F G H : Container ℓS ℓP

  _⊸⟨_⟩_ : (F : Container ℓS ℓP) {G H : Container ℓS ℓP} → F ⊸ G → G ⊸ H → F ⊸ H
  _⊸⟨_⟩_ F {G} {H} f g = _⋆_ {F = F} {G = G} {H = H} f g

  _⊸∎ : (F : Container ℓS ℓP) → F ⊸ F
  F ⊸∎ = id F
  {-# INLINE _⊸∎ #-}

  infixr 0 _⊸⟨_⟩_
  infix 1 _⊸∎

open ⊸Reasoning public
```

```agda
_⊸trunc_ : {n k : HLevel} → (F G : TruncatedContainer n k ℓS ℓP) → Type _
_⊸trunc_ F G = (F .fst) ⊸ (G .fst)

_⊸set_ : (F G : TruncatedContainer 2 2 ℓS ℓP) → Type _
_⊸set_ = _⊸trunc_ {n = 2} {k = 2}

isOfHLevel-⊸ : (n : HLevel) → {F G : TruncatedContainer n n ℓS ℓP} → isOfHLevel n (F ⊸trunc G)
isOfHLevel-⊸ n {F = _ , _ , trunc-pos-F} {G = _ , trunc-shape-G , trunc-pos-G} = isOfHLevelRetractFromIso n ⊸-Σ-Iso
  $ isOfHLevelΣ n
    (isOfHLevelΠ n λ _ → trunc-shape-G)
    λ f → isOfHLevelΠ n λ s → isOfHLevel≃ n (trunc-pos-G (f s)) (trunc-pos-F s)
```

### Equivalences

A linear morphism is an _equivalence_ if its shape map is an equivalence of types.
```agda
isContainerEquiv : ∀ {ℓS ℓT ℓP ℓQ} {F : Container ℓS ℓP} {G : Container ℓT ℓQ}
  → F ⊸ G → Type (ℓ-max ℓS ℓT)
isContainerEquiv f = isEquiv (f .shape)

isPropIsContainerEquiv : ∀ {ℓS ℓT ℓP ℓQ} {F : Container ℓS ℓP} {G : Container ℓT ℓQ}
  → {f : F ⊸ G} → isProp (isContainerEquiv f)
isPropIsContainerEquiv {f} = isPropIsEquiv (f .shape)
```

We wrap this in a new `record`, and use [`Equiv→⊸`](#Equiv→⊸) to project out the underlying morphism.
```agda
record Equiv (F G : Container ℓS ℓP) : Type (ℓ-max ℓS ℓP) where
  constructor [_◁≃_]
  field
    shape : F .Shape ≃ G .Shape
    pos : ∀ s → G .Pos (equivFun shape s) ≃ F .Pos s

Equiv→⊸ : {F G : Container ℓS ℓP} → Equiv F G → F ⊸ G
Equiv→⊸ [ shape ◁≃ pos ] .shape = equivFun shape
Equiv→⊸ [ shape ◁≃ pos ] .pos = pos
```

The two presentations convert into each other:
```agda
isContainerEquiv→Equiv : {F G : Container ℓS ℓP}
  → (f : F ⊸ G) → isContainerEquiv f → Equiv F G
isContainerEquiv→Equiv f is-equiv-f = [ (f .shape , is-equiv-f) ◁≃ f .pos ]

equivIsContainerEquiv : {F G : Container ℓS ℓP}
  → (e : Equiv F G) → isContainerEquiv (Equiv→⊸ e)
equivIsContainerEquiv e = equivIsEquiv (e .Equiv.shape)
```

Equivalences compose and there is an identity equivalence:
```agda
_⋆ₑ_ : ∀ {F G H : Container ℓS ℓP} → Equiv F G → Equiv G H → Equiv F H
(f ⋆ₑ g) .Equiv.shape = f .Equiv.shape ∙ₑ g .Equiv.shape
(f ⋆ₑ g) .Equiv.pos s = g .Equiv.pos (equivFun (f .Equiv.shape) s) ∙ₑ f .Equiv.pos s

idₑ : (F : Container ℓS ℓP) → Equiv F F
idₑ F .Equiv.shape = idEquiv _
idₑ F .Equiv.pos _ = idEquiv _
```

Additionally, we can invert equivalences of containers:
```agda
Equiv-inv : {F G : Container ℓS ℓ} → Equiv F G → Equiv G F
Equiv-inv {F} {G} [ shape ◁≃ pos ] .Equiv.shape = invEquiv shape
Equiv-inv {F} {G} [ shape ◁≃ pos ] .Equiv.pos t = invEquiv $ substEquiv (G .Pos) (sym (secEq shape t)) ∙ₑ pos (invEq shape t)
```

Again, we define some nice syntax for composing equivalences.
```agda
module EquivReasoning where
  private
    variable
      F G H : Container ℓS ℓP

  _⊸≃⟨_⟩_ : (F : Container ℓS ℓP) → Equiv F G → Equiv G H → Equiv F H
  _⊸≃⟨_⟩_ {G} {H} F f g = _⋆ₑ_ {F = F} {G = G} {H = H} f g

  _⊸≃∎ : (F : Container ℓS ℓP) → Equiv F F
  F ⊸≃∎ = idₑ F
  {-# INLINE _⊸≃∎ #-}

  _⊸≃⟨⟩_ : (F : Container ℓS ℓP) → Equiv F G → Equiv F G
  F ⊸≃⟨⟩ e = e

  infixr 0 _⊸≃⟨_⟩_
  infixr 0 _⊸≃⟨⟩_
  infix 1 _⊸≃∎

open EquivReasoning public
```

We can lift equivalences on types of shapes/positions to equivalences of containers:
```agda
Equiv-shape : ∀ {S S′ : Type ℓS} {P : S′ → Type ℓP}
  → (e : S ≃ S′)
  → Equiv (S ◁ (P ∘ equivFun e)) (S′ ◁ P)
Equiv-shape {P} e .Equiv.shape = e
Equiv-shape {P} e .Equiv.pos s = idEquiv (P (equivFun e s))

Equiv-pos : ∀ {S : Type ℓS} {P P′ : S → Type ℓP}
  → (e : ∀ s → P′ s ≃ P s)
  → Equiv (S ◁ P) (S ◁ P′)
Equiv-pos {S} e .Equiv.shape = idEquiv S
Equiv-pos {S} e .Equiv.pos = e
```

### Embeddings

A linear morphism is an _embedding_ of containers if its map of shapes is an embedding of types.
```agda
isContainerEmbedding : ∀ {ℓS ℓT ℓP ℓQ} {F : Container ℓS ℓP} {G : Container ℓT ℓQ}
  → F ⊸ G → Type (ℓ-max ℓS ℓT)
isContainerEmbedding f = isEmbedding (f .shape)
```

Every equivalence of containers is in particular an embedding.
```agda
isContainerEquiv→isContainerEmbedding : ∀ {ℓS ℓT ℓP ℓQ}
  → {F : Container ℓS ℓP} {G : Container ℓT ℓQ}
  → {f : F ⊸ G}
  → isContainerEquiv f
  → isContainerEmbedding f
isContainerEquiv→isContainerEmbedding = isEquiv→isEmbedding

Equiv→isContainerEmbedding : {F G : Container ℓS ℓP}
  → (e : Equiv F G)
  → isContainerEmbedding (Equiv→⊸ e)
Equiv→isContainerEmbedding e =
  isContainerEquiv→isContainerEmbedding
    {f = Equiv→⊸ e}
    (equivIsContainerEquiv e)
```

### More operations

We use a shorthand for \( \_ ⊗ \mathsf{Id} \).
```agda
_⊗Id : Container ℓS ℓP → Container ℓS ℓP
F ⊗Id = F ⊗ Id
```

This induces an action on linear morphisms.
```agda
[_]⊗_ :
  ∀ {F G : Container ℓS ℓP}
  → F ⊸ G
  → (H : Container ℓS ℓP)
  → (F ⊗ H) ⊸ (G ⊗ H)
[_]⊗_ {F} {G} f H .shape s = f .shape (s .fst) , _
[_]⊗_ {F} {G} f H .pos s = Sum.⊎-left-≃ (f .pos (s .fst))

[_]⊗Id : {F G : Container ℓS ℓP} → F ⊸ G → (F ⊗Id) ⊸ (G ⊗Id)
[_]⊗Id {ℓS} {ℓP} = [_]⊗ Id
```
