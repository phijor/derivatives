{-# OPTIONS --safe #-}
module Derivative.Prelude where

open import Cubical.Foundations.Prelude hiding (_◁_) public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Structure public
open import Cubical.Foundations.Isomorphism hiding (iso) public
open import Cubical.Foundations.Equiv renaming (_■ to _≃∎) public
open import Cubical.Foundations.HLevels public
open import Cubical.Functions.FunExtEquiv public
open import Cubical.Reflection.StrictEquiv public
open import Cubical.Data.Sigma using (_×_ ; ΣPathP ; Σ≡Prop ; ∃-syntax ; ∃!-syntax) public
open import Cubical.Relation.Nullary.Base using (¬_) public
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁) public

open import Cubical.Foundations.Equiv.Properties using (isPointedTarget→isEquiv→isEquiv)
import      Cubical.Data.Empty as Empty
open import Cubical.Data.Unit.Properties using (isContr→Iso2)
import      Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ : Level
    A A′ B C : Type ℓ

data 𝟘* {ℓ : Level} : Type ℓ where

𝟘 : Type
𝟘 = 𝟘* {ℓ-zero}
{-# DISPLAY 𝟘* {ℓ = ℓ-zero} = 𝟘 #-}

ex-falso : Empty.⊥ → A
ex-falso ()

record 𝟙* {ℓ : Level} : Type ℓ where
  constructor • -- \bub

𝟙 : Type
𝟙 = 𝟙* {ℓ-zero}
{-# DISPLAY 𝟙* {ℓ = ℓ-zero} = 𝟙 #-}

-- refl with explicit argument
refl′ : (a : A) → a ≡ a
refl′ a i = a

-- type ascription `the A a : A`
the : (A : Type ℓ) → (a : A) → A
the A a = a
{-# INLINE the #-}

_≢_ : (a b : A) → Type _
a ≢ b = ¬ a ≡ b

≢-rec : ∀ {ℓB} {B : Type ℓB} {a b : A} → a ≡ b → a ≢ b → B
≢-rec eq neq = Empty.rec (neq eq)

isProp≢ : ∀ {a b : A} → isProp (a ≢ b)
isProp≢ {a} {b} p q i x = Empty.isProp⊥ (p x) (q x) i

-- A step in equivalence reasoning for definitional identity equivalences
_≃⟨⟩_ : ∀ {ℓ ℓ'} (A : Type ℓ) {B : Type ℓ'} → A ≃ B → A ≃ B
A ≃⟨⟩ e = e
infixr 0 _≃⟨⟩_

ℓ-of : ∀ {ℓ} (A : Type ℓ) → Level
ℓ-of {ℓ} _ = ℓ

ℓ-at : ∀ {ℓ} {A : Type ℓ} (a : A) → Level
ℓ-at {ℓ} _ = ℓ

-- Diagrammatic composition of functions (non-dependent)
_⨟_ : (f : A → B) (g : B → C) → A → C
f ⨟ g = λ a → g (f a)
infixl 9 _⨟_

-- Diagrammatic composition of functions (dependent)
_⨟ᴰ_ : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : A → Type ℓB} {C : ∀ a → B a → Type ℓC}
  → (f : (a : A) → B a)
  → (g : {a : A} → (b : B a) → C a b)
  → (a : A) → C a (f a)
f ⨟ᴰ g = λ a → g (f a)
infixl 9 _⨟ᴰ_

{- "Composition reasoning":

Write composites of functions without forgetting intermediate types.
Given f : A → B, g : B → C, e : C ≃ C', their composite A → C' is
  
  A →⟨ f ⟩ B →⟨ g ⟩ C →≃⟨ e ⟩ C' →∎
-}
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

-- Unfortunately, the Cubical library indexes truncation levels starting from (0 = contractible),
-- whereas they are (-2)-indexed in HoTT-book parlance.  To avoid confusion, we can give names to
-- the lowest levels.
pattern h-prop = 1
pattern h-set = 2
pattern h-groupoid = 3

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

equivExt : {e f : A ≃ B} → (∀ x → equivFun e x ≡ equivFun f x) → e ≡ f
equivExt = equivEq ∘ funExt

contractDomainEquiv : isContr A → (A → B) ≃ B
contractDomainEquiv is-contr-A = isoToEquiv (isContr→Iso2 is-contr-A)

hSet≡ : ∀ {X Y : hSet ℓ} → ⟨ X ⟩ ≡ ⟨ Y ⟩ → X ≡ Y
hSet≡ = Σ≡Prop (λ X → isPropIsSet)

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
