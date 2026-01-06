{-# OPTIONS --safe #-}
module Derivative.Basics.Unit where

open import Derivative.Prelude

open import Cubical.Foundations.Univalence

private
  variable
    ℓ : Level
    A : Type ℓ

isContr-𝟙* : isContr (𝟙* {ℓ})
isContr-𝟙* .fst = •
isContr-𝟙* .snd _ = refl

isOfHLevel-𝟙* : ∀ n → isOfHLevel n (𝟙* {ℓ})
isOfHLevel-𝟙* n = isContr→isOfHLevel n isContr-𝟙*

isProp-𝟙* : isProp (𝟙* {ℓ})
isProp-𝟙* = isOfHLevel-𝟙* 1

isSet-𝟙* : isSet (𝟙* {ℓ})
isSet-𝟙* = isOfHLevel-𝟙* 2

𝟙*-unit-×-left-equiv : (𝟙* {ℓ} × A) ≃ A
𝟙*-unit-×-left-equiv = strictEquiv (λ { (• , a) → a }) (λ a → (• , a))

isContr→≡𝟙* : isContr A → A ≡ 𝟙*
isContr→≡𝟙* contr-A = ua $ (const •) , is-equiv-const where
  is-equiv-const : isEquiv (λ _ → •)
  is-equiv-const .equiv-proof • .fst = contr-A .fst , refl
  is-equiv-const .equiv-proof • .snd (a , p) = ΣPathP (contr-A .snd a , λ i j → •)
