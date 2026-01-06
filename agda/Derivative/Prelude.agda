{-# OPTIONS --safe #-}
module Derivative.Prelude where

open import Cubical.Foundations.Prelude hiding (_◁_ ; hcomp ; comp) public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Structure public
open import Cubical.Foundations.Isomorphism hiding (iso) public
open import Cubical.Foundations.Equiv renaming (_■ to _≃∎) public
open import Cubical.Foundations.HLevels public
open import Cubical.Reflection.StrictEquiv public
open import Cubical.Data.Sigma using (_×_ ; ΣPathP ; Σ≡Prop ; ∃-syntax ; ∃!-syntax) public
open import Cubical.Relation.Nullary.Base using (¬_) public

import      Cubical.Core.Primitives as Primitives
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma hiding (hcomp ; comp)
import      Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Base using (ℕ ; zero ; suc)
open import Cubical.Data.Unit.Properties using (isContr→Iso2)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

private
  variable
    ℓ : Level
    A A′ B C : Type ℓ

hcompᴵ : (φ : I) (u : ∀ i → Partial (φ ∨ ~ i) A) → A
hcompᴵ {A} φ u = Primitives.hcomp {φ = φ} sys base module hcomp where
  base : A
  base = u i0 1=1
  {-# INLINE base #-}

  sys : I → Partial φ A
  sys i (φ = i1) = u i 1=1

compᴵ : (A : I → Type ℓ) (φ : I) (u : ∀ i → Partial (φ ∨ ~ i) (A i)) → A i1
compᴵ A φ u = Primitives.comp A {φ = φ} sys base module comp where
  base : A i0
  base = u i0 1=1
  {-# INLINE base #-}

  sys : (i : I) → Partial φ (A i)
  sys i (φ = i1) = u i 1=1

∂ᴵ : I → I
∂ᴵ i = i ∨ ~ i

doubleCompPathP : (B : A → Type ℓ)
  → {x y z w : A}
  → {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} {s : x ≡ w}
  → (filler : Square (sym p) r q s)
  → {xᴰ : B x} {yᴰ : B y} {zᴰ : B z} {wᴰ : B w}
  → (pᴰ : PathP (λ i → B (p i)) xᴰ yᴰ)
  → (qᴰ : PathP (λ i → B (q i)) yᴰ zᴰ)
  → (rᴰ : PathP (λ i → B (r i)) zᴰ wᴰ)
  → PathP (λ i → B (s i)) xᴰ wᴰ
doubleCompPathP B filler pᴰ qᴰ rᴰ i =
  compᴵ (λ j → B (filler i j)) (∂ᴵ i)
  λ where
    j (i = i0) → pᴰ (~ j)
    j (i = i1) → rᴰ j
    j (j = i0) → qᴰ i

module _
  {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {l : a₀₀ ≡ a₀₁} {r : a₁₀ ≡ a₁₁}
  {b : a₀₀ ≡ a₁₀} {t : a₀₁ ≡ a₁₁}
  where
  flipSquareH : Square l r b t → Square (sym l) (sym r) t b
  flipSquareH sq i j = sq i (~ j)

data 𝟘* {ℓ : Level} : Type ℓ where

𝟘 = 𝟘* {ℓ-zero}
{-# DISPLAY 𝟘* {ℓ-zero} = 𝟘 #-}

ex-falso : Empty.⊥ → A
ex-falso ()

record 𝟙* {ℓ : Level} : Type ℓ where
  constructor • -- \bub

𝟙 : Type
𝟙 = 𝟙* {ℓ-zero}
{-# DISPLAY 𝟙* {ℓ-zero} = 𝟙 #-}

-- refl with explicit argument
refl′ : (a : A) → a ≡ a
refl′ a i = a

Jᴰ : ∀ {ℓ ℓ'} {A : I → Type ℓ}
  → (x : A i0)
  → (P : ∀ {i : I} → (y : A i) → PathP (λ j → A (i ∧ j)) x y → Type ℓ')
  → (d : P x refl)
  → {y : A i1} (p : PathP A x y) → P y p
Jᴰ _ P d p = transport (λ i → P (p i) λ j → p (i ∧ j)) d

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

symEquiv : ∀ {a b : A} → (a ≡ b) ≃ (b ≡ a)
symEquiv = strictEquiv sym sym

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

substAdjointEquiv : (B : A → Type ℓ) {x y : A} (p : x ≡ y)
  → {x′ : B x} {y′ : B y}
  → (subst B p x′ ≡ y′) ≃ (x′ ≡ subst B (sym p) y′)
substAdjointEquiv B {x} {y} p {x′} {y′} = invEquiv (equivAdjointEquiv (substEquiv' B p) {x′} {y′})

neqCongEquiv : {a b : A} {x y : B}
  → (a ≡ b) ≃ (x ≡ y)
  → (a ≢ b) ≃ (x ≢ y)
neqCongEquiv e = preCompEquiv (invEquiv e)

equivExt : {e f : A ≃ B} → (∀ x → equivFun e x ≡ equivFun f x) → e ≡ f
equivExt = equivEq ∘ funExt

contractDomainEquiv : isContr A → (A → B) ≃ B
contractDomainEquiv is-contr-A = isoToEquiv (isContr→Iso2 is-contr-A)

⨟-fiber-equiv : (f : A → B) → (g : B → C) → ∀ c → fiber (f ⨟ g) c ≃ (Σ[ (b , _) ∈ fiber g c ] fiber f b)
⨟-fiber-equiv {A} {B} {C} f g c =
  Σ[ a ∈ A ] g (f a) ≡ c
    ≃⟨ Σ-cong-equiv-snd (λ a → invEquiv (Σ-contractFst (isContrSingl (f a)))) ⟩
  Σ[ a ∈ A ] Σ[ (b , _) ∈ singl (f a) ] g b ≡ c
    ≃⟨ strictEquiv
      (λ { (a , (b , p) , q) → ((b , q) , a , p) })
      (λ { ((b , q) , a , p) → (a , (b , p) , q) })
    ⟩
  Σ[ (b , _) ∈ fiber g c ] fiber f b
    ≃∎

postCompFiberEquiv : (f : A → B) → (ψ : C → B) → (∀ c → fiber f (ψ c)) ≃ fiber (f ∘_) ψ
postCompFiberEquiv {A} {C} f ψ =
  (∀ c → Σ[ a ∈ A ] f a ≡ ψ c)
    ≃⟨ Σ-Π-≃ ⟩
  Σ[ φ ∈ (C → A) ] (∀ c → f (φ c) ≡ ψ c)
    ≃⟨ Σ-cong-equiv-snd (λ φ → funExtEquiv) ⟩
  Σ[ φ ∈ (C → A) ] f ∘ φ ≡ ψ
    ≃∎

isEquiv-∘ : ∀ {f : A → B} {g : B → C}
  → isEquiv g
  → isEquiv f
  → isEquiv (g ∘ f)
isEquiv-∘ {f} {g} is-equiv-g is-equiv-f = equivIsEquiv (compEquiv (f , is-equiv-f) (g , is-equiv-g))

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
