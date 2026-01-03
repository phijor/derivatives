{-# OPTIONS --safe #-}
module Derivative.Bag where

open import Derivative.Prelude renaming (⊤ to ⊤*)
open import Derivative.Container
open import Derivative.Derivative
open import Derivative.Isolated
open import Derivative.Remove
open import Derivative.Basics.Decidable as Dec
open import Derivative.Basics.Maybe

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
          fin-equiv = replace-isolated-equiv x₀ (isIsolatedFin {X = X} x₀)

          fin-path : (X -ᶠ x₀) +ᶠ 𝟙 ≡ X
          fin-path = equivFun (FinSet≡ _ _) $ ua fin-equiv

          pt-path : PathP (λ i → ⟨ fin-path i ⟩) nothing x₀
          pt-path = ua-gluePath fin-equiv $ refl′ x₀

∂-pos-equiv : (X : FinSet) (x : ⟨ X ⟩ °) → (⟨ X ⟩ ∖ (x .fst)) ≃ ⟨ X -ᶠ (x .fst) ⟩
∂-pos-equiv X x = idEquiv _

∂-Bag-equiv : Equiv (∂ Bag) Bag
∂-Bag-equiv .Equiv.shape = ∂-shape-equiv
∂-Bag-equiv .Equiv.pos = uncurry ∂-pos-equiv

private
  ⊤ = ⊤* ℓ-zero

module Universe (P : Type → Type)
  (is-prop-P : ∀ A → isProp (P A))
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
    U-equiv = replace-isolated-equiv x₀ isolated-x₀

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

  isSub-⊤ : isSub ⊤
  isSub-⊤ = PT.∣ const 0 , hasPropFibers→isEmbedding (λ { n (tt* , _) (tt* , _) → Σ≡Prop (λ _ → isSetℕ _ _) refl }) ∣₁

  isSub-+1 : ∀ {X} → isSub X → isSub (X ⊎ ⊤)
  isSub-+1 {X} = PT.map _+1 where module _ (ι : X ↪ ℕ) where
    suc-ι : (X ⊎ ⊤) → ℕ
    suc-ι (just x) = suc (ι .fst x)
    suc-ι nothing = 0

    _+1 : (X ⊎ ⊤) ↪ ℕ
    _+1 .fst = suc-ι
    _+1 .snd = injEmbedding isSetℕ cancel where
      cancel : ∀ {x y : X ⊎ ⊤} → suc-ι x ≡ suc-ι y → x ≡ y
      cancel {x = just x} {y = just y} p = cong just (isEmbedding→Inj (ι .snd) x y (injSuc p))
      cancel {x = just x} {y = nothing} = ex-falso ∘ snotz
      cancel {x = nothing} {y = just y} = ex-falso ∘ znots
      cancel {x = nothing} {y = nothing} _ = refl′ nothing

  isSub-∖ : ∀ {X} → isSub X → ∀ x → isSub (X ∖ x)
  isSub-∖ {X} = PT.rec (isPropΠ λ x → isPropIsSub (X ∖ x)) λ ι x → PT.∣ compEmbedding ι (remove-embedding x) ∣₁

  open Universe isSub isPropIsSub isSub-+1 isSub-∖
    renaming (uBag to ℕBag)

  ∂-ℕBag : Equiv (∂ ℕBag) ℕBag
  ∂-ℕBag = ∂-uBag

{-
module SubV where
  open import Derivative.Sum
  open import Derivative.W

  open V using (V ; El)

  V-Bag : Container (ℓ-suc ℓ-zero) ℓ-zero
  V-Bag .Container.Shape = V
  V-Bag .Container.Pos = El

  is-isolated-inh-suc : ∀ A → isIsolated (V.inh-suc A)
  is-isolated-inh-suc (sup A f) = isIsolatedNothing

  is-isolated-𝟘 : isIsolated V.𝟘
  is-isolated-𝟘 (sup A f) = {! !}

  pred : (Σ[ A ∈ V ] (El A °)) → V
  pred (A , a₀ , _) = A V.- a₀

  suc : V → Σ[ A ∈ V ] (El A °)
  suc A = (A V.+1) , V.inh-suc A , is-isolated-inh-suc A

  sec : section pred suc
  sec (sup A f) = WPath→≡ _ _ (ua removeNothingEquiv , ua→ λ { ((just a) , _) → refl′ (f a) ; (nothing , nothing≢nothing) → ex-falso $ nothing≢nothing refl })

  ret : retract pred suc
  ret (sup A f , x°) = ΣPathP (WPath→≡ _ _ (ua (unreplace-isolated-equiv (x° .fst) (x° .snd)) , ua→ λ { (just a) → refl ; nothing → {!ret _  !} }) , {! !})
  -- ret (sup A f , x°) = ΣPathP (sym (WPath→≡ _ _ (ua (replace-isolated-equiv (x° .fst) (x° .snd)) , ua→ bar)) , {! !})
    where
      bar : (a : A) → f a ≡ V.+1-El (f ∘ fst) (replace-isolated (x° .fst) (x° .snd) a)
      bar a = Dec.rec (λ p → {! replace?-yes (x° .fst) (x° .snd) !}) (λ h → sym $ cong (V.+1-El (f ∘ fst)) (replace?-no (x° .fst) (x° .snd) (a , h))) (x° .snd a)
        -- cong (V.+1-El (f ∘ fst)) (sym $ replace?-no (x° .fst) (x° .snd) (a , {! !}))
      foo : (a : Maybe (A - x°)) → W-branch ((sup A f) V.+1) (⊎-map-left fst a) ≡ f (unreplace-isolated (x° .fst) a)
      foo (just a) = refl′ (f (a .fst))
      foo nothing = {! !}

  ∂-V-Bag-shape-Iso : Iso (Σ[ A ∈ V ] (El A °)) V
  ∂-V-Bag-shape-Iso .Iso.fun = pred
  ∂-V-Bag-shape-Iso .Iso.inv = suc
  ∂-V-Bag-shape-Iso .Iso.rightInv = sec
  ∂-V-Bag-shape-Iso .Iso.leftInv = ret

  ∂-V : Equiv (∂ V-Bag) V-Bag
  ∂-V = {! !}
-}
