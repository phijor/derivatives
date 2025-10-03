module Derivative.Maybe where

open import Derivative.Prelude
open import Derivative.Isolated
open import Derivative.Decidable
open import Derivative.Remove

open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)

private
  variable
    ℓ : Level
    A B : Type ℓ

Maybe : (A : Type ℓ) → Type ℓ
Maybe {ℓ} A = A ⊎ ⊤ ℓ

pattern nothing = inr tt*
pattern just x = inl x

maybe-equiv : A ≃ B → Maybe A ≃ Maybe B
maybe-equiv e = Sum.⊎-equiv e $ invEquiv LiftEquiv ∙ₑ LiftEquiv

nothing≢just : {a : A} → the (Maybe A) nothing ≢ (just a)
nothing≢just nothing≡just = Sum.⊎Path.encode _ _ nothing≡just .lower

isIsolatedNothing : isIsolated {A = Maybe A} nothing
isIsolatedNothing (just a) = no nothing≢just
isIsolatedNothing nothing = yes refl

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

module _ {ℓ} {A : Type ℓ} (a₀ : A) (a₀≟_ : isIsolated a₀) where
  private
    replace? : (a : A) → Dec (a₀ ≡ a) → Maybe (A ∖ a₀)
    replace? a (yes _) = nothing
    replace? a (no a₀≢a) = just (a , a₀≢a)

    replace?-yes : replace? a₀ (a₀≟ a₀) ≡ nothing
    replace?-yes = cong (replace? a₀) $ isIsolated→isPropDecPath a₀ a₀≟_ a₀ (a₀≟ a₀) (yes refl)

    replace?-no : (a : A ∖ a₀) → replace? (a .fst) (a₀≟ a .fst) ≡ just a
    replace?-no (a , a₀≢a) = cong (replace? a) $ isIsolated→isPropDecPath a₀ a₀≟_ a (a₀≟ a) (no a₀≢a)
    
  replace-isolated : A → Maybe (A ∖ a₀)
  replace-isolated a = replace? a (a₀≟ a)
    
  replace-isolated' : A → Maybe (A ∖ a₀)
  replace-isolated' a with (a₀≟ a)
  ... | (yes _) = nothing
  ... | (no a₀≢a) = just (a , a₀≢a)

  replace-isolated'-β-no : {a : A} → (a₀≢a : a₀ ≢ a) → replace-isolated' a ≡ just (a , a₀≢a)
  replace-isolated'-β-no {a} a₀≢a with (a₀≟ a)
  ... | (yes a₀≡a) = ex-falso $ a₀≢a a₀≡a
  ... | (no a₀≢a) = congS just (Remove≡ (refl′ a))

  unreplace-isolated : Maybe (A ∖ a₀) → A
  unreplace-isolated (just (a , _)) = a
  unreplace-isolated nothing = a₀

  replace-isolated'-Iso : Iso A (Maybe (A ∖ a₀))
  replace-isolated'-Iso .Iso.fun = replace-isolated'
  replace-isolated'-Iso .Iso.inv = unreplace-isolated
  replace-isolated'-Iso .Iso.rightInv (just (a , a₀≢a)) with a₀≟ a
  ... | (yes a₀≡a) = ex-falso (a₀≢a a₀≡a)
  ... | (no a₀≢a') = congS just $ ΣPathP (refl′ a , isProp¬ _ a₀≢a' a₀≢a)
  replace-isolated'-Iso .Iso.rightInv nothing with a₀≟ a₀
  ... | (yes a₀≡a₀) = refl
  ... | (no a₀≢a₀) = ex-falso $ a₀≢a₀ refl
  replace-isolated'-Iso .Iso.leftInv a with (a₀≟ a)
  ... | (yes a₀≡a) = a₀≡a
  ... | (no  a₀≢a) = refl′ a

  replace-isolated-Iso : Iso A (Maybe (A ∖ a₀))
  replace-isolated-Iso .Iso.fun = replace-isolated
  replace-isolated-Iso .Iso.inv = unreplace-isolated
  replace-isolated-Iso .Iso.rightInv (just a) = replace?-no a
  replace-isolated-Iso .Iso.rightInv nothing = replace?-yes
  replace-isolated-Iso .Iso.leftInv a with (a₀≟ a)
  ... | (yes a₀≡a) = a₀≡a
  ... | (no  a₀≢a) = refl′ a

  replace-isolated-equiv : A ≃ (Maybe (A ∖ a₀))
  replace-isolated-equiv = isoToEquiv replace-isolated-Iso

  replace-isolated'-equiv : A ≃ (Maybe (A ∖ a₀))
  replace-isolated'-equiv = isoToEquiv replace-isolated'-Iso
