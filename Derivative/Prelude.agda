module Derivative.Prelude where

open import Cubical.Foundations.Prelude hiding (_◁_) public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Structure public
open import Cubical.Foundations.Isomorphism hiding (iso) public
open import Cubical.Foundations.Equiv renaming (_■ to _≃∎) public
open import Cubical.Foundations.HLevels public
open import Cubical.Reflection.StrictEquiv public

open import Cubical.Data.Sigma using (_×_ ; ΣPathP ; Σ≡Prop) public
import      Cubical.Data.Empty as Empty
open import Cubical.Data.Unit.Base
open import Cubical.Data.Unit.Base using (tt*) public

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
