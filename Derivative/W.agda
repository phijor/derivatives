{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Derivative.W where

open import Derivative.Prelude
open import Derivative.Decidable
open import Derivative.Sum

open import Cubical.Data.Empty.Base as Empty using (⊥*)
open import Cubical.Data.Sigma.Properties using (discreteΣ)
open import Cubical.Relation.Nullary.Properties using (EquivPresDiscrete)

private
  variable
    ℓS ℓP ℓQ : Level

private
  module impl (S : Type ℓS) (P : S → Type ℓP) where
    data W : Type (ℓ-max ℓS ℓP) where
      sup : (s : S) (f : P s → W) → W

  module implᴰ (S : Type ℓS) (P : S → Type ℓP) (Q : S → Type ℓQ) where
    open impl S P

    data Wᴰ : W → Type (ℓ-max ℓQ (ℓ-of W)) where
      top : {s : S} {f : P s → W} → (q : Q s) → Wᴰ (sup s f)
      below : {s : S} {f : P s → W} → (p : P s) → (wᴰ : Wᴰ (f p)) → Wᴰ (sup s f)

module _ {S : Type ℓS} {P : S → Type ℓP} where
  open impl S P

  W-elim : ∀ {ℓ} {B : W → Type ℓ}
    → (sup* : (s : S) (f : P s → W) → (sup* : (p : P s) → B (f p)) → B (sup s f))
    → (w : W) → B w
  W-elim {B} sup* (sup s f) = sup* s f λ p → W-elim {B = B} sup* (f p)

  W-elim2 : ∀ {ℓ} {B : W → W → Type ℓ}
    → (sup* : (s₀ s₁ : S) (f₀ : P s₀ → W) (f₁ : P s₁ → W)
      → (sup* : (p₀ : P s₀) → (p₁ : P s₁) → B (f₀ p₀) (f₁ p₁))
      → B (sup s₀ f₀) (sup s₁ f₁)
      )
    → (w₀ w₁ : W) → B w₀ w₁
  W-elim2 {B} sup* (sup s₀ f₀) (sup s₁ f₁) = sup* s₀ s₁ f₀ f₁ λ p₀ p₁ → W-elim2 {B = B} sup* (f₀ p₀) (f₁ p₁)

  W-out : W → (Σ[ s ∈ S ] (P s → W))
  W-out (sup s f) = s , f

  W-shape : W → S
  W-shape = fst ∘ W-out

  W-branch : (w : W) → P (W-shape w) → W
  W-branch = snd ∘ W-out

  W-in : (Σ[ s ∈ S ] (P s → W)) → W
  W-in = uncurry sup

  W-in-equiv : (Σ[ s ∈ S ] (P s → W)) ≃ W
  W-in-equiv = isoToEquiv iso module W-in-equiv where
    iso : Iso (Σ[ s ∈ S ] (P s → W)) W
    iso .Iso.fun = W-in
    iso .Iso.inv = W-out
    iso .Iso.rightInv (sup s f) = refl
    iso .Iso.leftInv _ = refl

  W-out-equiv : W ≃ (Σ[ s ∈ S ] (P s → W))
  W-out-equiv = isoToEquiv (invIso W-in-equiv.iso)

module _ {S : Type ℓS} {P : S → Type ℓP} where
  open impl
  WPath : (x y : W S P) → Type (ℓ-max ℓS ℓP)
  WPath (sup s₀ f₀) (sup s₁ f₁) = Σ (s₀ ≡ s₁) λ p → PathP (λ i → P (p i) → W S P) f₀ f₁

  ≡→WPath : (x y : W S P) → x ≡ y → WPath x y
  ≡→WPath (sup s₀ f₀) (sup s₁ f₁) x≡y .fst = cong W-shape x≡y
  ≡→WPath (sup s₀ f₀) (sup s₁ f₁) x≡y .snd = cong W-branch x≡y

  WPath→≡ : (x y : W S P) → WPath x y → x ≡ y
  WPath→≡ (sup s₀ f₀) (sup s₁ f₁) (s₀≡s₁ , f₀≡f₁) = cong₂ sup s₀≡s₁ f₀≡f₁

  WPath-linv-refl : (x : W S P) → WPath→≡ x x (≡→WPath x x refl) ≡ refl
  WPath-linv-refl (sup s f) = refl

  WPath-linv : (x y : W S P) (p : x ≡ y) → WPath→≡ _ _ (≡→WPath _ _ p) ≡ p
  WPath-linv x y = J (λ y p → WPath→≡ _ _ (≡→WPath _ _ p) ≡ p) $ WPath-linv-refl x

  WPath-rinv : (x y : W S P) (p : WPath x y) → ≡→WPath _ _ (WPath→≡ _ _ p) ≡ p
  WPath-rinv (sup s₀ f₀) (sup s₁ f₁) _ = refl

  WPathIso : (x y : W S P) → Iso (x ≡ y) (WPath x y)
  WPathIso x y .Iso.fun = ≡→WPath _ _
  WPathIso x y .Iso.inv = WPath→≡ _ _
  WPathIso x y .Iso.rightInv = WPath-rinv _ _
  WPathIso x y .Iso.leftInv = WPath-linv _ _

module _ (S : Type ℓS) (P : S → Type ℓP) (Q : S → Type ℓQ) where
  open impl S P
  open implᴰ S P Q

  module _ (s : S) (f : P s → W) where
    Wᴰ-out : Wᴰ (sup s f) → Q s ⊎ (Σ[ p ∈ P s ] (Wᴰ (f p)))
    Wᴰ-out (top q) = inl q
    Wᴰ-out (below p wᴰ) = inr (p , wᴰ)

    Wᴰ-in : Q s ⊎ (Σ[ p ∈ P s ] (Wᴰ (f p))) → Wᴰ (sup s f)
    Wᴰ-in (inl q) = top q
    Wᴰ-in (inr (p , wᴰ)) = below p wᴰ

    Wᴰ-out-equiv : Wᴰ (sup s f) ≃ Q s ⊎ (Σ[ p ∈ P s ] (Wᴰ (f p)))
    Wᴰ-out-equiv = isoToEquiv iso module Wᴰ-out-equiv where
      iso : Iso _ _
      iso .Iso.fun = Wᴰ-out
      iso .Iso.inv = Wᴰ-in
      iso .Iso.rightInv (inl _) = refl
      iso .Iso.rightInv (inr _) = refl
      iso .Iso.leftInv (top _) = refl
      iso .Iso.leftInv (below _ _) = refl

    Wᴰ-in-equiv : Q s ⊎ (Σ[ p ∈ P s ] (Wᴰ (f p))) ≃ Wᴰ (sup s f)
    Wᴰ-in-equiv = isoToEquiv (invIso Wᴰ-out-equiv.iso)

    isEquiv-Wᴰ-in : isEquiv Wᴰ-in
    isEquiv-Wᴰ-in = equivIsEquiv Wᴰ-in-equiv

  module _ (disc-P : ∀ s → Discrete (P s)) (disc-Q : ∀ s → Discrete (Q s)) where
    discrete-Wᴰ : ∀ w → Discrete (Wᴰ w)
    discrete-Wᴰ (sup s f) = EquivPresDiscrete (Wᴰ-in-equiv s f) $
      discrete⊎
        (disc-Q s)
        (discreteΣ (disc-P s) (discrete-Wᴰ ∘ f))

  Wᴰ-Path : ∀ {w₀ w₁} (h : WPath w₀ w₁) → (x : Wᴰ w₀) → (y : Wᴰ w₁) → Type (ℓ-max ℓS (ℓ-max ℓP ℓQ))
  Wᴰ-Path {w₀ = sup s₀ f₀} {w₁ = sup s₁ f₁} (s₀≡s₁ , f₀≡f₁) (top q₀) (top q₁) = Lift {j = ℓ-max ℓS ℓP} $ PathP (λ i → Q (s₀≡s₁ i)) q₀ q₁
  Wᴰ-Path {w₀ = sup s₀ f₀} {w₁ = sup s₁ f₁} (s₀≡s₁ , f₀≡f₁) (top q₀) (below p₁ y) = ⊥*
  Wᴰ-Path {w₀ = sup s₀ f₀} {w₁ = sup s₁ f₁} (s₀≡s₁ , f₀≡f₁) (below p₀ x) (top q₁) = ⊥*
  Wᴰ-Path {w₀ = sup s₀ f₀} {w₁ = sup s₁ f₁} (s₀≡s₁ , f₀≡f₁) (below p₀ x) (below p₁ y)
    = Σ[ p₀≡p₁ ∈ PathP (λ i → P (s₀≡s₁ i)) p₀ p₁ ] PathP (λ i → Wᴰ (f₀≡f₁ i (p₀≡p₁ i))) x y

open impl public using (W ; sup)
open implᴰ public using (Wᴰ ; top ; below)
