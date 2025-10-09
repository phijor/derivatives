module Derivative.Prelude where

open import Cubical.Foundations.Prelude hiding (_◁_) public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Structure public
open import Cubical.Foundations.Isomorphism hiding (iso) public
open import Cubical.Foundations.Equiv renaming (_■ to _≃∎) public
open import Cubical.Foundations.HLevels public
open import Cubical.Reflection.StrictEquiv public
open import Cubical.Data.Sigma using (_×_ ; ΣPathP ; Σ≡Prop ; ∃-syntax) public
open import Cubical.Data.Unit.Base using (tt*) public
open import Cubical.Relation.Nullary.Base using (¬_) public

open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
import      Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Base
open import Cubical.Data.Unit.Base

private
  variable
    ℓ : Level
    A B C : Type ℓ


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

module PathReasoning where
  ≡⟨⟩∎-syntax : ∀ (x y : A) → x ≡ y → x ≡ y
  ≡⟨⟩∎-syntax _ _ p = p
  {-# INLINE ≡⟨⟩∎-syntax #-}

  infixr 3 ≡⟨⟩∎-syntax
  syntax ≡⟨⟩∎-syntax x y p = x ≡⟨ p ⟩∎ y ∎

open PathReasoning using (≡⟨⟩∎-syntax) public

-- A step in equivalence reasoning for definitional identity equivalences
_≃⟨⟩_ : ∀ {ℓ ℓ'} (A : Type ℓ) {B : Type ℓ'} → A ≃ B → A ≃ B
A ≃⟨⟩ e = e
infixr 0 _≃⟨⟩_

symEquiv : ∀ {a b : A} → (a ≡ b) ≃ (b ≡ a)
symEquiv = strictEquiv sym sym

ℓ-of : ∀ {ℓ} (A : Type ℓ) → Level
ℓ-of {ℓ} _ = ℓ

-- Diagrammatic composition of functions (non-dependent)
_⨟_ : (f : A → B) (g : B → C) → A → C
f ⨟ g = λ a → g (f a)
infixl 9 _⨟_

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

⊤ : (ℓ : Level) → Type ℓ
⊤ _ = Unit*

ex-falso : Empty.⊥ → A
ex-falso ()

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

private
  variable
    A′ : Type ℓ
    
Σ-map-fst : ∀ {B′ : A′ → Type ℓ} (f : A → A′) → (Σ A (B′ ∘ f)) → (Σ A′ B′)
Σ-map-fst f (a , b′) = (f a , b′)

module _ {ℓB ℓB′} {A : Type ℓ} {B : A → Type ℓB} {B′ : A → Type ℓB′} where
  Σ-map-snd : (f : ∀ a → B a → B′ a) → (Σ A B) → (Σ A B′)
  Σ-map-snd f (a , b) = (a , f a b)

  Σ-map-snd-fiber-iso : ∀ {f : ∀ a → B a → B′ a} {a′ : A} {b′ : B′ a′} → Iso (fiber (Σ-map-snd f) (a′ , b′)) (fiber (f a′) b′)
  Σ-map-snd-fiber-iso {f} {a′} {b′} = fiber-iso where
      shuffle : Iso _ (Σ[ (a , p) ∈ singl a′ ] Σ[ b ∈ B a ] PathP (λ i → B′ (p (~ i))) (f a b) b′)
      shuffle .Iso.fun ((a , b) , (p , q)) = (a , sym p) , b , q
      shuffle .Iso.inv ((a , p) , b , q) = (a , b) , sym p , q
      shuffle .Iso.rightInv _ = refl
      shuffle .Iso.leftInv _ = refl

      fiber-iso : Iso (fiber (Σ-map-snd f) (a′ , b′)) (fiber (f a′) b′)
      fiber-iso =
        _
          Iso⟨ Σ-cong-iso-snd (λ (a , b) → invIso ΣPathPIsoPathPΣ) ⟩
        Σ[ (a , b) ∈ Σ A B ] Σ[ p ∈ a ≡ a′ ] PathP (λ i → B′ (p i)) (f a b) b′
          Iso⟨ shuffle ⟩
        Σ[ (a , p) ∈ singl a′ ] Σ[ b ∈ B a ] PathP (λ i → B′ (p (~ i))) (f a b) b′
          Iso⟨ Σ-contractFstIso (isContrSingl a′) ⟩
        _
          ∎Iso

  isEquiv-Σ-map-snd : {f : ∀ a → B a → B′ a} → (∀ a → isEquiv (f a)) → isEquiv (Σ-map-snd f)
  isEquiv-Σ-map-snd {f} is-equiv-f .equiv-proof (a′ , b′) = isOfHLevelRetractFromIso 0 Σ-map-snd-fiber-iso (is-equiv-f a′ .equiv-proof b′)

  opaque
    isEquiv-Σ-map-snd→isEquiv : {f : ∀ a → B a → B′ a} → isEquiv (Σ-map-snd f) → ∀ a → isEquiv (f a)
    isEquiv-Σ-map-snd→isEquiv {f} is-equiv-Σ-map-snd a′ .equiv-proof b′ = isOfHLevelRetractFromIso 0
      (invIso Σ-map-snd-fiber-iso)
      (is-equiv-Σ-map-snd .equiv-proof (a′ , b′))

Σ-map : ∀ {ℓB ℓB′} {B : A → Type ℓB} {B′ : A′ → Type ℓB′}
  → (e : A → A′)
  → (f : ∀ a → B a → B′ (e a))
  → Σ A B → Σ A′ B′
Σ-map e f (a , b) .fst = e a
Σ-map e f (a , b) .snd = f a b

isOfHLevelSucΣSndProp : ∀ {ℓB} {B : A → Type ℓB} (n : HLevel)
  → isOfHLevel (suc n) A
  → (∀ a → isProp (B a))
  → isOfHLevel (suc n) (Σ A B)
isOfHLevelSucΣSndProp n is-trunc-A is-prop-B = isOfHLevelΣ (suc n) is-trunc-A λ a → isProp→isOfHLevelSuc n (is-prop-B a)

hSet≡ : ∀ {X Y : hSet ℓ} → ⟨ X ⟩ ≡ ⟨ Y ⟩ → X ≡ Y
hSet≡ = Σ≡Prop (λ X → isPropIsSet)
