{-# OPTIONS --safe #-}
module Derivative.Basics.Function where

open import Derivative.Prelude

open import Cubical.Data.Sigma.Properties

private
  variable
    ℓ : Level
    A B C : Type ℓ

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
