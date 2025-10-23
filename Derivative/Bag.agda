module Derivative.Bag where

open import Derivative.Prelude renaming (⊤ to ⊤*)
open import Derivative.Container
open import Derivative.Derivative
open import Derivative.Isolated
open import Derivative.Remove
open import Derivative.Decidable
open import Derivative.Maybe

open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary using (isProp¬)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (inl ; inr ; _⊎_)
open import Cubical.Data.FinSet as FinSet renaming (FinSet to FinSet*)
open import Cubical.Data.FinSet.Induction as Fin renaming (_+_ to _+ᶠ_)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (tt*)

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

_-ᶠ_ : (X : FinSet) → (x : ⟨ X ⟩) → FinSet
(X -ᶠ x) .fst = ⟨ X ⟩ ∖ x
(X -ᶠ x) .snd = isFinSetMinus (str X) x

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
      pred (X , x) = X -ᶠ x

      suc : FinSet → Σ FinSet ⟨_⟩
      suc X .fst = X +ᶠ 𝟙
      suc X .snd = nothing

      pred-iso : Iso (Σ FinSet ⟨_⟩) FinSet
      pred-iso .Iso.fun = pred
      pred-iso .Iso.inv = suc
      pred-iso .Iso.rightInv X = equivFun (FinSet≡ _ _) $ ua $ removeNothingEquiv
      pred-iso .Iso.leftInv (X , x₀) = ΣPathP λ where
          .fst → fin-path
          .snd → pt-path
        where
          fin-equiv : ⟨ (X -ᶠ x₀) +ᶠ 𝟙 ⟩ ≃ ⟨ X ⟩
          fin-equiv = invEquiv $ replace-isolated-equiv x₀ (isIsolatedFin {X = X} x₀)

          fin-path : (X -ᶠ x₀) +ᶠ 𝟙 ≡ X
          fin-path = equivFun (FinSet≡ _ _) $ ua fin-equiv

          pt-path : PathP (λ i → ⟨ fin-path i ⟩) nothing x₀
          pt-path = ua-gluePath fin-equiv $ refl′ x₀

∂-pos-equiv : (X : FinSet) (x : ⟨ X ⟩ °) → (⟨ X ⟩ ∖ (x .fst)) ≃ ⟨ X -ᶠ (x .fst) ⟩
∂-pos-equiv X x = idEquiv _

∂-Bag-map : Equiv (∂ Bag) Bag
∂-Bag-map .Equiv.shape = ∂-shape-equiv
∂-Bag-map .Equiv.pos = uncurry ∂-pos-equiv

private
  ⊤ = ⊤* ℓ-zero

module Universe (P : Type → Type)
  (is-prop-P : ∀ A → isProp (P A))
  -- (is-P-⊎ : ∀ {A B : Type} → P A → P B → P (A ⊎ B))
  -- (is-P-⊤ : P ⊤)
  (is-P-+1 : ∀ {A : Type} → P A → P (A ⊎ ⊤))
  (is-P-∖ : ∀ {A : Type} → P A → ∀ a → P (A ∖ a))
  where
  U : Type₁
  U = Σ[ X ∈ Type ] P X

  uBag : Container (ℓ-suc ℓ-zero) ℓ-zero
  uBag .Container.Shape = U
  uBag .Container.Pos = ⟨_⟩

  _-ᵁ_ : (X : U) → (x : ⟨ X ⟩) → U
  (X -ᵁ x) .fst = ⟨ X ⟩ ∖ x
  (X -ᵁ x) .snd = is-P-∖ (str X) x

  -- _+ᵁ_ : (X Y : U) → U
  -- (X +ᵁ Y) .fst = ⟨ X ⟩ ⊎ ⟨ Y ⟩
  -- (X +ᵁ Y) .snd = is-P-⊎ (str X) (str Y)

  -- ⊤ᵁ : U
  -- ⊤ᵁ .fst = ⊤
  -- ⊤ᵁ .snd = is-P-⊤

  _+1 : U → U
  (X +1) .fst = ⟨ X ⟩ ⊎ ⊤
  (X +1) .snd = is-P-+1 (str X)

  ∂-uBag-shape-Iso : Iso (Σ[ X ∈ U ] (⟨ X ⟩ °)) U
  ∂-uBag-shape-Iso .Iso.fun (X , x , _) = X -ᵁ x
  ∂-uBag-shape-Iso .Iso.inv X .fst = X +1
  ∂-uBag-shape-Iso .Iso.inv X .snd = nothing°
  ∂-uBag-shape-Iso .Iso.rightInv X = Σ≡Prop is-prop-P $ ua $ removeNothingEquiv
  ∂-uBag-shape-Iso .Iso.leftInv (X , x°@(x₀ , isolated-x₀)) = ΣPathP (U-path , pt-path) where
    U-equiv : (⟨ X ⟩ ∖ x₀) ⊎ ⊤ ≃ ⟨ X ⟩
    U-equiv = invEquiv (replace-isolated-equiv x₀ isolated-x₀)

    U-path : (X -ᵁ x₀) +1 ≡ X
    U-path = Σ≡Prop is-prop-P $ ua U-equiv

    pt-path : PathP (λ i → ⟨ U-path i ⟩ °) nothing° x°
    pt-path = IsolatedPathP {B = ⟨_⟩} {p = U-path} (ua-gluePath U-equiv (refl′ x₀))

  ∂-uBag-shape : (Σ[ X ∈ U ] (⟨ X ⟩ °)) ≃ U
  ∂-uBag-shape = isoToEquiv ∂-uBag-shape-Iso

  ∂-uBag : Equiv (∂ uBag) uBag
  ∂-uBag .Equiv.shape = ∂-uBag-shape
  ∂-uBag .Equiv.pos (X , x , _) = idEquiv ⟨ X -ᵁ x ⟩

module SubNat where
  open import Cubical.Data.Nat
  open import Cubical.Functions.Embedding
  open import Cubical.HITs.PropositionalTruncation as PT

  isSub : (X : Type) → Type _
  isSub X = ∥ X ↪ ℕ ∥₁

  isPropIsSub : ∀ X → isProp (isSub X)
  isPropIsSub X = isPropPropTrunc

  -- XXX: Interleaving embedding
  isSub-⊎ : ∀ {X Y} → isSub X → isSub Y → isSub (X ⊎ Y)
  isSub-⊎ {X} {Y} = PT.map2 λ ι κ → {! !}

  isSub-⊤ : isSub ⊤
  isSub-⊤ = PT.∣ const 0 , hasPropFibers→isEmbedding (λ { n (tt* , _) (tt* , _) → Σ≡Prop (λ _ → isSetℕ _ _) refl }) ∣₁

  isSub-+1 : ∀ {X} → isSub X → isSub (X ⊎ ⊤)
  isSub-+1 {X} = PT.map _+1 where module _ (ι : X ↪ ℕ) where
    _+1 : (X ⊎ ⊤) ↪ ℕ
    _+1 .fst (just x) = suc (ι .fst x)
    _+1 .fst nothing = 0
    _+1 .snd = hasPropFibersOfImage→isEmbedding λ where
      (just x) → {! !}
      nothing (just x , p) y → {! !}
      nothing (nothing , p) y → {! !}

  isSub-∖ : ∀ {X} → isSub X → ∀ x → isSub (X ∖ x)
  isSub-∖ {X} = PT.rec {! !} λ ι x → PT.∣ compEmbedding ι (remove-embedding x) ∣₁

  open Universe isSub isPropIsSub isSub-+1 isSub-∖
    renaming (uBag to ℕBag)

  ∂-ℕBag : Equiv (∂ ℕBag) ℕBag
  ∂-ℕBag = ∂-uBag
