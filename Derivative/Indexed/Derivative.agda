module Derivative.Indexed.Derivative where

open import Derivative.Prelude
open import Derivative.Decidable
open import Derivative.Isolated
open import Derivative.Remove

open import Derivative.Indexed.Container


private
  variable
    ℓ : Level
    Ix : Type ℓ

∂ : (i : Ix °) → (F : Container ℓ Ix) → Container ℓ Ix
∂ {ℓ} {Ix} (i , i≟_) F = shape ◁ pos module ∂ where
  open Container F renaming (Shape to S ; Pos to P)
  shape : Type ℓ
  shape = Σ[ s ∈ S ] ((P i s) °)

  pos-dec : (j : Ix) → Dec (i ≡ j) → shape → Type _
  pos-dec j (yes i≡j) (s , p , _) = P i s ∖ p
  pos-dec j (no  i≢j) (s , p , _) = P j s

  pos : Ix → shape → Type _
  pos j = pos-dec j (i≟ j)

∂-map : (i : Ix °) → {F G : Container ℓ Ix} → (F ⊸ G) → (∂ i F ⊸ ∂ i G)
∂-map (i , i≟_) {F} {G} φ = [ shape ⊸ pos ] module ∂-map where
  module φ = _⊸_ φ

  shape : Σ _ _ → Σ _ _
  shape = Σ-map φ.shape λ s → invEq (IsolatedSubstEquiv (φ.pos i s))

  pos-dec : ∀ j → (i≟j : Dec (i ≡ j)) → ∀ s → ∂.pos-dec i i≟_ G j i≟j (shape s) ≃ ∂.pos-dec i i≟_ F j i≟j s
  pos-dec j (yes i≡j) (s , p , _) = RemoveRespectEquiv p (φ.pos i s)
  pos-dec j (no ¬i≡j) (s , _) = φ.pos j s

  pos : ∀ j s → _ ≃ _
  pos j = pos-dec j (i≟ j)

isEquiv-∂-map : (i : Ix °) {F G : Container ℓ Ix}
  → {f : F ⊸ G}
  → isContainerEquiv f
  → isContainerEquiv (∂-map i f)
isEquiv-∂-map = {! !}

∂-map-equiv : (i : Ix °) {F G : Container ℓ Ix}
  → (e : F ⧟ G)
  → ∂ i F ⧟ ∂ i G
∂-map-equiv i f =
  [ shape , isEquiv-∂-map i {f = Equiv.as-⊸ f} (equivIsContainerEquiv f)
    ◁≃ pos
  ]
  where
    open ∂-map (i .fst) (i .snd) (Equiv.as-⊸ f)
