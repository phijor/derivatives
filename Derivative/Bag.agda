module Derivative.Bag where

open import Derivative.Prelude
open import Derivative.Container
open import Derivative.Derivative
open import Derivative.Isolated
open import Derivative.Remove
open import Derivative.Decidable
open import Derivative.Maybe

open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary using (isProp¬)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (inl ; inr)
open import Cubical.Data.FinSet as FinSet renaming (FinSet to FinSet*)
open import Cubical.Data.FinSet.Induction as Fin
open import Cubical.Data.FinSet.Constructors

private
  FinSet = FinSet* ℓ-zero

Bag : Container (ℓ-suc ℓ-zero) ℓ-zero
Bag .Container.Shape = FinSet
Bag .Container.Pos = ⟨_⟩

-- X ∖ x is a decidable subtype of X, hence a finite set
isFinSetMinus : ∀ {X : Type} → isFinSet X → ∀ x → isFinSet (X ∖ x)
isFinSetMinus {X} is-finset-X x = isFinSetΣ (X , is-finset-X) λ x′ → (¬ x ≡ x′) , is-finset-≢ x′
  where
    is-finset-≢ : ∀ x′ → isFinSet (x ≢ x′)
    is-finset-≢ x′ = isDecProp→isFinSet (isProp¬ _) (decNot (isFinSet→Discrete is-finset-X x x′))

_-_ : (X : FinSet) → (x : ⟨ X ⟩) → FinSet
(X - x) .fst = ⟨ X ⟩ ∖ x
(X - x) .snd = isFinSetMinus (str X) x

IsolatedFinEquiv : (X : FinSet) → ⟨ X ⟩ ° ≃ ⟨ X ⟩
IsolatedFinEquiv (X , is-finset) = Discrete→IsolatedEquiv $ isFinSet→Discrete {A = X} is-finset

isIsolatedFin : ∀ {X : FinSet} (x₀ : ⟨ X ⟩) → isIsolated x₀
isIsolatedFin {X} = Discrete→isIsolated (isFinSet→Discrete (str X))

∂-shape-equiv : (Σ[ X ∈ FinSet ] (⟨ X ⟩ °)) ≃ FinSet
∂-shape-equiv =
  Σ[ X ∈ FinSet ] ⟨ X ⟩ °
    ≃⟨ Σ-cong-equiv-snd IsolatedFinEquiv ⟩
  Σ[ X ∈ FinSet ] ⟨ X ⟩
    ≃⟨ isoToEquiv pred-iso ⟩
  FinSet
    ≃∎
    where
      pred : Σ FinSet ⟨_⟩ → FinSet
      pred (X , x) = X - x

      suc : FinSet → Σ FinSet ⟨_⟩
      suc X .fst = X Fin.+ 𝟙
      suc X .snd = nothing

      pred-iso : Iso (Σ FinSet ⟨_⟩) FinSet
      pred-iso .Iso.fun = pred
      pred-iso .Iso.inv = suc
      pred-iso .Iso.rightInv X = equivFun (FinSet≡ _ _) $ ua $ removeNothingEquiv
      pred-iso .Iso.leftInv (X , x₀) = ΣPathP λ where
          .fst → fin-path
          .snd → pt-path
        where
          fin-equiv : ⟨ (X - x₀) Fin.+ 𝟙 ⟩ ≃ ⟨ X ⟩
          fin-equiv = invEquiv $ replace-isolated-equiv x₀ (isIsolatedFin {X = X} x₀)

          fin-path : (X - x₀) Fin.+ 𝟙 ≡ X
          fin-path = equivFun (FinSet≡ _ _) $ ua fin-equiv

          pt-path : PathP (λ i → ⟨ fin-path i ⟩) nothing x₀
          pt-path = ua-gluePath fin-equiv $ refl′ x₀

∂-pos-equiv : (X : FinSet) (x : ⟨ X ⟩ °) → (⟨ X ⟩ ∖ (x .fst)) ≃ ⟨ X - (x .fst) ⟩
∂-pos-equiv X x = idEquiv _

∂-Bag-map : Equiv (∂ Bag) Bag
∂-Bag-map .Equiv.shape = ∂-shape-equiv
∂-Bag-map .Equiv.pos = uncurry ∂-pos-equiv
