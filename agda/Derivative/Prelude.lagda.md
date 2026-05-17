```agda
{-# OPTIONS --safe #-}
module Derivative.Prelude where
```

## Re-exports

```agda
open import Cubical.Foundations.Prelude hiding (_◁_) public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Structure public
open import Cubical.Foundations.Isomorphism hiding (iso) public
open import Cubical.Foundations.Equiv renaming (_■ to _≃∎) public
open import Cubical.Reflection.StrictEquiv public
open import Cubical.Data.Sigma using (_×_ ; ΣPathP ; Σ≡Prop ; ∃-syntax ; ∃!-syntax) public
open import Cubical.Relation.Nullary.Base using (¬_) public
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁) public
```

<!--
```agda
open import Cubical.Foundations.Equiv.Properties using (isPointedTarget→isEquiv→isEquiv)
import      Cubical.Data.Empty as Empty
import      Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ : Level
    A A′ B C : Type ℓ
```
-->

## Base types

We use custom universe-polymorphic types for the empty- and unit type to minimize the amount of conversions
we have to perform between `Unit` and `Lift Unit` (and similarly for `⊥`).

The single inhabitant of `𝟙*` is `•` (`\bub`). We explicitly make use η-equality for the unit type.
```agda
data 𝟘* {ℓ : Level} : Type ℓ where

record 𝟙* {ℓ : Level} : Type ℓ where
  eta-equality
  constructor •
```

In the base universe `Type`, we use the non-starred aliases `𝟘` and `𝟙`.
```agda
𝟘 : Type
𝟘 = 𝟘* {ℓ-zero}
{-# DISPLAY 𝟘* {ℓ = ℓ-zero} = 𝟘 #-}

𝟙 : Type
𝟙 = 𝟙* {ℓ-zero}
{-# DISPLAY 𝟙* {ℓ = ℓ-zero} = 𝟙 #-}
```

## Conveniences

Get the universe level of a type.
```agda
ℓ-of : ∀ {ℓ} (A : Type ℓ) → Level
ℓ-of {ℓ} _ = ℓ
```
Useful when `A` is a variable and introducing it would obscure a declaration:
```agda
private
  Example : (a : A) → Type (ℓ-of A)
  Example a = ∀ b → a ≡ b
```

A type ascription: to document that `a` has type `A`, write `the A a`.
```agda
the : (A : Type ℓ) → (a : A) → A
the A a = a
{-# INLINE the #-}
```

The constant path with an explicit argument:
```agda
refl′ : (a : A) → a ≡ a
refl′ a i = a
```

## Negation and inequality

Negation `¬_` is defined in terms of the non-polymorphic empty type `⊥`.
Use `ex-falso` to eliminate it.
```agda
ex-falso : Empty.⊥ → A
ex-falso ()
```

Inequality is negation of propositional equality and always an _h_-proposition.
```agda
_≢_ : (a b : A) → Type _
a ≢ b = ¬ a ≡ b

isProp≢ : ∀ {a b : A} → isProp (a ≢ b)
isProp≢ {a} {b} p q i x = Empty.isProp⊥ (p x) (q x) i
```

Having both `p : a ≡ b` and `¬p : a ≢ b` is absurd.
```agda
≢-rec : ∀ {ℓB} {B : Type ℓB} {a b : A} → a ≡ b → a ≢ b → B
≢-rec eq neq = Empty.rec (neq eq)
```

## Functions

Diagrammatic composition of functions, non-dependent:
```agda
_⨟_ : (f : A → B) (g : B → C) → A → C
f ⨟ g = λ a → g (f a)
infixl 9 _⨟_
```

Diagrammatic composition of functions, dependent:
```agda
_⨟ᴰ_ : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : A → Type ℓB} {C : ∀ a → B a → Type ℓC}
  → (f : (a : A) → B a)
  → (g : {a : A} → (b : B a) → C a b)
  → (a : A) → C a (f a)
f ⨟ᴰ g = λ a → g (f a)
infixl 9 _⨟ᴰ_
```

### Composition reasoning

Write composites of functions without forgetting intermediate types.
```agda
_→⟨_⟩_ : (A : Type ℓ) → (A → B) → (B → C) → (A → C)
_ →⟨ f ⟩ g = f ⨟ g

_→≃⟨_⟩_ : (A : Type ℓ) → (A ≃ B) → (B → C) → (A → C)
_ →≃⟨ e ⟩ g = equivFun e ⨟ g

_→∎ : (A : Type ℓ) → A → A
A →∎ = λ a → a
{-# INLINE _→∎ #-}

infixr 0 _→⟨_⟩_
infixr 0 _→≃⟨_⟩_
infix 1 _→∎
```

This lets us write a composite like this:
```agda
private module _ (e : A′ ≃ A) (f : A → B) (g : B → C) where
  _ : A′ → C
  _ =
    A′
      →≃⟨ e ⟩
    A
      →⟨ f ⟩
    B
      →⟨ g ⟩
    C
      →∎
```

We compose equivalences in a similar manner, but add a no-op step for definitionally equal types:
```agda
_≃⟨⟩_ : ∀ {ℓ ℓ'} (A : Type ℓ) {B : Type ℓ'} → A ≃ B → A ≃ B
A ≃⟨⟩ e = e
infixr 0 _≃⟨⟩_

private module _ (e₁ : A ≃ 𝟙* {ℓ-zero}) (e₂ : 𝟙 ≃ B) where
  _ : A ≃ B
  _ =
    A
      ≃⟨ e₁ ⟩
    𝟙* {ℓ-zero}
      ≃⟨⟩
    𝟙
      ≃⟨ e₂ ⟩
    B
      ≃∎
```

### Function extensionality

Equivalences are equal if and only if their underlying maps are pointwise equal:
```agda
equivExt : {e f : A ≃ B} → (∀ x → equivFun e x ≡ equivFun f x) → e ≡ f
equivExt = equivEq ∘ funExt
```

Function extensionality, [`funExt`](Cubical.Foundations.Prelude.html#funExt), is an equivalence:
```agda
open import Cubical.Functions.FunExtEquiv public
```

This generalizes to path spaces of paths, i.e. squares:
```agda
module _
  {ℓA ℓB} {A : Type ℓA} {B : A → (i j : I) → Type ℓB}
  {f₀₀ : ∀ a → B a i0 i0}
  {f₀₁ : ∀ a → B a i0 i1}
  {f₀₋ : PathP (λ j → ∀ a → B a i0 j) f₀₀ f₀₁}
  {f₁₀ : ∀ a → B a i1 i0}
  {f₁₁ : ∀ a → B a i1 i1}
  {f₁₋ : PathP (λ j → ∀ a → B a i1 j) f₁₀ f₁₁}
  {f₋₀ : PathP (λ i → ∀ a → B a i i0) f₀₀ f₁₀}
  {f₋₁ : PathP (λ i → ∀ a → B a i i1) f₀₁ f₁₁} where

  funExtSquare :
      (f : (a : A) → SquareP (B a) (λ j → f₀₋ j a) (λ j → f₁₋ j a) (λ i → f₋₀ i a) (λ i → f₋₁ i a))
    → SquareP (λ i j → (a : A) → B a i j) f₀₋ f₁₋ f₋₀ f₋₁
  funExtSquare f i j a = f a i j

  funExtSquare⁻ :
      (sq : SquareP (λ i j → (a : A) → B a i j) f₀₋ f₁₋ f₋₀ f₋₁)
    → ((a : A) → SquareP (B a) (λ j → f₀₋ j a) (λ j → f₁₋ j a) (λ i → f₋₀ i a) (λ i → f₋₁ i a))
  funExtSquare⁻ sq a i j = sq i j a

  funExtSquareEquiv :
    ((a : A) → SquareP (B a) (λ j → f₀₋ j a) (λ j → f₁₋ j a) (λ i → f₋₀ i a) (λ i → f₋₁ i a))
      ≃
    (SquareP (λ i j → (a : A) → B a i j) f₀₋ f₁₋ f₋₀ f₋₁)
  unquoteDef funExtSquareEquiv = defStrictEquiv funExtSquareEquiv funExtSquare funExtSquare⁻
```

## Truncation levels of types

```agda
open import Cubical.Foundations.HLevels public
```

Unfortunately, the Cubical library indexes truncation levels starting from (0 = contractible),
whereas they are (-2)-indexed in HoTT-book parlance.
To avoid confusion, we give names to the lowest levels.
```agda
pattern h-prop = 1
pattern h-set = 2
pattern h-groupoid = 3
```

Also, here's some useful properties of _h_-propositions:
```agda
isPropFromPointed→isProp : (A → isProp A) → isProp A
isPropFromPointed→isProp h a b = h a a b

isContr≃mereInh×isProp : isContr A ≃ (∥ A ∥₁ × isProp A)
isContr≃mereInh×isProp = propBiimpl→Equiv
  isPropIsContr
  (isProp× PT.isPropPropTrunc isPropIsProp)
  (λ is-contr-A → PT.∣ is-contr-A .fst ∣₁ , isContr→isProp is-contr-A)
  (uncurry $ PT.rec (isProp→ isPropIsContr) inhProp→isContr)

isContr≃inh×isProp : isContr A ≃ (A × isProp A)
isContr≃inh×isProp .fst is-contr-A = is-contr-A .fst , isContr→isProp is-contr-A
isContr≃inh×isProp .snd = isPointedTarget→isEquiv→isEquiv _ λ where
  (a₀ , is-prop-A) → equivIsEquiv $ propBiimpl→Equiv isPropIsContr (isProp× is-prop-A isPropIsProp) _ (uncurry inhProp→isContr)
```
