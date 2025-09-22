module Derivative.Isolated where

open import Derivative.Prelude
open import Derivative.Decidable
  as Dec
  using
    ( locallyDiscrete→locallyIsPropPath
    ; Dec ; yes ; no
    ; Discrete
    ; _≢_
    )
open import Derivative.Remove


open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary.Properties using (EquivPresDec)

private
  variable
    ℓ : Level
    A B : Type ℓ

isIsolated : (a : A) → Type _
isIsolated a = ∀ b → Dec (a ≡ b)

-- There is at most one path to an isolated point:
isIsolated→isPropPath : (a : A) → isIsolated a → ∀ a′ → isProp (a ≡ a′)
isIsolated→isPropPath = locallyDiscrete→locallyIsPropPath

-- For an isolated point, decidability of equality is a proposition:
isIsolated→isPropDecPath : (a : A) → isIsolated a → ∀ a′ → isProp (Dec (a ≡ a′))
isIsolated→isPropDecPath a isolated a′ = Dec.isPropDec (isIsolated→isPropPath a isolated a′)

-- Being isolated is a proposition:
isPropIsIsolated : (a : A) → isProp (isIsolated a)
isPropIsIsolated a = isPropFromPointed→isProp go where
  go : isIsolated a → isProp (isIsolated a)
  go isolated = isPropΠ $ isIsolated→isPropDecPath a isolated

Isolated : (A : Type ℓ) → Type ℓ
Isolated A = Σ[ a ∈ A ] isIsolated a

_° : (A : Type ℓ) → Type ℓ
A ° = Isolated A

Isolated≡ : ∀ {a b : A °} → a .fst ≡ b .fst → a ≡ b
Isolated≡ = Σ≡Prop isPropIsIsolated

Isolated≢ : ∀ {a b : A °} → a .fst ≢ b .fst → a ≢ b
Isolated≢ a≢b p = a≢b $ cong fst p

DiscreteIsolated : Discrete (Isolated A)
DiscreteIsolated (a , a≟_) (b , b≟_) = Dec.map Isolated≡ Isolated≢ (a≟ b)

opaque
  isSetIsolated : isSet (A °)
  isSetIsolated = Dec.Discrete→isSet DiscreteIsolated

module _ (_≟_ : Discrete A) where
  Discrete→isIsolated : ∀ a → isIsolated a
  Discrete→isIsolated = _≟_

  Discrete→IsolatedEquiv : A ° ≃ A
  Discrete→IsolatedEquiv = Σ-contractSnd λ a → inhProp→isContr (Discrete→isIsolated a) (isPropIsIsolated a)

opaque
  isIsolatedRespectEquiv : (e : A ≃ B) → (b : B) → isIsolated b → isIsolated (invEq e b)
  isIsolatedRespectEquiv e b isolated a = EquivPresDec eqv (isolated (equivFun e a))
    where
      eqv : (b ≡ equivFun e a) ≃ (invEq e b ≡ a)
      eqv = symEquiv ∙ₑ invEquiv (equivAdjointEquiv e) ∙ₑ symEquiv

remove-emb : (a : A) → A ∖ a → A
remove-emb a = fst
