{-# OPTIONS --safe #-}
module Derivative.Basics.Maybe where

open import Derivative.Prelude
open import Derivative.Basics.Decidable as Dec
open import Derivative.Remove
open import Derivative.Basics.Sum as Sum using (_⊎_ ; inl ; inr)

private
  variable
    ℓ : Level
    A B : Type ℓ

-- TODO: Banish nothing : Maybe A into the lowest universe.
Maybe : (A : Type ℓ) → Type ℓ
Maybe {ℓ} A = A ⊎ ⊤ ℓ

pattern nothing = inr tt*
pattern just x = inl x

maybe-equiv : A ≃ B → Maybe A ≃ Maybe B
maybe-equiv e = Sum.⊎-equiv e $ invEquiv LiftEquiv ∙ₑ LiftEquiv

nothing≢just : {a : A} → the (Maybe A) nothing ≢ (just a)
nothing≢just nothing≡just = Sum.⊎Path.encode _ _ nothing≡just .lower

remove-nothing : Maybe A ∖ nothing → A
remove-nothing ((just a) , _) = a
remove-nothing (nothing , nothing≢nothing) = ex-falso (nothing≢nothing refl)

isEquivRemoveNothing : isEquiv (remove-nothing {A = A})
isEquivRemoveNothing .equiv-proof a = contr-fib where
  contr-fib : isContr (fiber remove-nothing a)
  contr-fib .fst = (just a , nothing≢just) , refl
  contr-fib .snd ((just b , _) , b≡a) = ΣPathP λ where
    .fst → Remove≡ $ cong just (sym b≡a)
    .snd → λ i j → b≡a (~ i ∨ j)
  contr-fib .snd ((nothing , nothing≢nothing) , _) = ex-falso (nothing≢nothing refl)

removeNothingEquiv : Maybe A ∖ nothing ≃ A
removeNothingEquiv .fst = remove-nothing
removeNothingEquiv .snd = isEquivRemoveNothing

unreplace-isolated : (a₀ : A) → Maybe (A ∖ a₀) → A
unreplace-isolated a₀ (just (a , _)) = a
unreplace-isolated a₀ nothing = a₀
