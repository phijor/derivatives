{-# OPTIONS -WnoUnsupportedIndexedMatch --safe #-}
module Derivative.Indexed.List where

open import Derivative.Prelude
open import Derivative.Basics.W
open import Derivative.Basics.Sum
open import Derivative.Basics.Unit
open import Derivative.Basics.Decidable using (Discrete ; yes)
open import Derivative.Isolated.Base
open import Derivative.Indexed.Container
open import Derivative.Indexed.Derivative
open import Derivative.Indexed.Mu
open import Derivative.Indexed.MuRule

import Cubical.Data.Nat as ℕ
import Cubical.Data.Sigma as Σ
import Cubical.Data.Empty as Empty

private
  data S : Type where
    nil cons : S

  pattern x = ₀
  pattern y = ₁

  X : S → Type
  X nil = 𝟘
  X cons = 𝟙

  Y : S → Type
  Y nil = 𝟘
  Y cons = 𝟙

  L : Container ℓ-zero 𝟚
  L .Container.Shape = S
  L .Container.Pos x = X
  L .Container.Pos y = Y

  Fin : ℕ → Type
  Fin zero = 𝟘
  Fin (suc n) = 𝟙 ⊎ Fin n

  depth : W S Y → ℕ
  depth = W-rec λ where
    (nil , _) → 0
    (cons , n) → suc (n •)

  L-shape-equiv : W S Y ≃ ℕ
  L-shape-equiv = isoToEquiv λ where
    .Iso.fun → depth
    .Iso.inv → ℕ.elim (sup nil (λ ())) λ n w → sup cons λ _ → w
    .Iso.rightInv → ℕ.elim refl λ n → cong suc
    .Iso.leftInv → W-elim λ where
      nil f ind → cong (sup nil) $ funExt λ ()
      cons f ind → cong (sup cons) $ funExt ind

  unique-tree-of-depth : ∀ n → isContr (fiber depth n)
  unique-tree-of-depth = equivIsEquiv L-shape-equiv .equiv-proof

  L-pos-equiv : (x : W S Y) → Fin (depth x) ≃ Wᴰ S Y X x
  L-pos-equiv = W-elim λ where
    nil f _ → Empty.uninhabEquiv (λ ()) λ where
      (top p) → 𝟘-rec p
      (below p q) → 𝟘-rec p
    cons f ind-≃ →
      𝟙 ⊎ Fin (depth (f •))
        ≃⟨ ⊎-right-≃ $ ind-≃ • ⟩
      𝟙 ⊎ (Wᴰ S Y X (f •))
        ≃⟨ ⊎-right-≃ $ invEquiv $ Σ.Σ-contractFst isContr-𝟙* ⟩
      𝟙 ⊎ (Σ[ p ∈ 𝟙 ] Wᴰ S Y X (f p))
        ≃⟨ Wᴰ-in-equiv _ _ _ cons f ⟩
      Wᴰ S Y X (sup cons f)
        ≃∎

  discrete-L : ∀ ix s → Discrete (L .Container.Pos ix s)
  discrete-L x nil ()
  discrete-L y nil ()
  discrete-L x cons • • = yes refl
  discrete-L y cons • • = yes refl

List : Container ℓ-zero 𝟙
List .Container.Shape = ℕ
List .Container.Pos _ n = Fin n

μL⧟List : μ L ⧟ List
μL⧟List .Equiv.shape = L-shape-equiv
μL⧟List .Equiv.pos _ = L-pos-equiv
