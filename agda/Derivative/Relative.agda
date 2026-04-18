{-# OPTIONS --allow-unsolved-metas --lossy-unification #-}
module Derivative.Relative where

open import Derivative.Prelude
open import Derivative.Container

open import Derivative.Remove

open import Derivative.Basics.Equiv
open import Derivative.Basics.Sigma
open import Derivative.Basics.Sum
open import Derivative.Basics.DecidableEmbedding

open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Sigma


private
  variable
    ℓ : Level
    F H G : Container ℓ ℓ

module _ (R : Type ℓ) where
  ∂ : Container ℓ ℓ → Container ℓ ℓ
  ∂ F = S′ ◁ P′ where
    open module F = Container F renaming (Shape to S ; Pos to P)

    S′ : Type _
    S′ = Σ[ s ∈ S ] (R ↪° P s)

    P′ : S′ → Type _
    P′ (s , f , _) = P s - f

  ∂[_] : {F G : Container ℓ ℓ} → Cart F G → Cart (∂ F) (∂ G)
  ∂[_] {F} {G} φ = ∂f module ∂[-] where
    open Container
    open Cart φ renaming (shape to f ; pos to u)

    shape : (Σ[ s ∈ F .Shape ] R ↪° F .Pos s) → (Σ[ t ∈ G .Shape ] R ↪° G .Pos t)
    shape (s , _) .fst = f s
    shape (s , p) .snd = dec-emb-postcomp-equiv p $ invEquiv (u s)

    pos : (s : F .Shape) (p : R → F .Pos s) → (G .Pos (f s) - (p ⨟ invEq (u s))) ≃ (F .Pos s - p)
    pos s p = complementSubstEquiv' p (u s)

    ∂f : Cart (∂ F) (∂ G)
    ∂f .Cart.shape = shape
    ∂f .Cart.pos ∂s = pos (∂s .fst) (∂s .snd .fst)
    {-# INLINE ∂f #-}

  module _ (F : Container ℓ ℓ) where
    open Cart
    private
      open module F = Container F renaming (Shape to S ; Pos to P)

    unit-shape : S → Σ[ (s , _) ∈ S × 𝟙* {ℓ} ] (R ↪° (P s ⊎ R))
    unit-shape s .fst = s , •
    unit-shape s .snd = inr-dec-emb

    unit-pos : (s : S) → ((P s ⊎ R) - inr) ≃ P s
    unit-pos s = invEquiv sum-inr-remove-equiv

    unit : Cart F (∂ (F ⊗ 𝕪 R))
    unit .shape = unit-shape
    unit .pos = unit-pos

  is-natural-unit : (F G : Container ℓ ℓ) (f : Cart F G) → (unit F) ⋆ ∂[ [ f ]⊗ 𝕪 R ] ≡ f ⋆ unit G
  is-natural-unit F G f = Cart≡ (funExt λ s → ΣPathP (refl′ (f .Cart.shape s , •) , ↪°-≡ (refl′ inr)))
    $ funExt λ s → equivExt λ where
      (inl q , _) → refl′ $ equivFun (f .Cart.pos s) q
      (inr r , ¬inr≡inr) → ex-falso $ ¬inr≡inr (r , refl)

  module _ (G : Container ℓ ℓ) where
    open Cart
    private
      open module G = Container G renaming (Shape to T ; Pos to Q)

    counit-shape : (Σ[ t ∈ T ] (R ↪° Q t)) × 𝟙* {ℓ} → T
    counit-shape ((t , _ , _) , _) = t

    counit-pos : ∀ (t : T) (f : R ↪° Q t)  → Q t ≃ ((Q t - f .fst) ⊎ R)
    counit-pos t f = invEquiv (remove-sum-left-equiv f)

    counit : Cart (∂ G ⊗ 𝕪 R) G
    counit .shape = counit-shape
    counit .pos ((t , f) , _) = counit-pos t f

  zig : (F : Container ℓ ℓ) → Cart (F ⊗ 𝕪 R) (F ⊗ 𝕪 R)
  zig F =
    (F ⊗ 𝕪 R)           ⊸⟨ [ unit F ]⊗ 𝕪 R ⟩
    (∂ (F ⊗ 𝕪 R) ⊗ 𝕪 R) ⊸⟨ counit (F ⊗ 𝕪 R) ⟩
    (F ⊗ 𝕪 R)           ⊸∎

  zig≡ : (F : Container ℓ ℓ) → ([ unit F ]⊗ (𝕪 R)) ⋆ counit (F ⊗ 𝕪 R) ≡ id (F ⊗ 𝕪 R)
  zig≡ F = Cart≡ refl (funExt pos-path) module zig≡ where
    pos-path : ∀ s → (counit-pos (F ⊗ 𝕪 R) s inr-dec-emb) ∙ₑ ⊎-left-≃ (unit-pos F (s .fst)) ≡ idEquiv _
    pos-path s = equivExt λ where
      (inl p) → refl′ $ inl p
      (inr r) → refl′ $ inr r

  zag≡ : (G : Container ℓ ℓ) → unit (∂ G) ⋆ ∂[ counit G ] ≡ id (∂ G)
  zag≡ G = Cart≡ (funExt shape-path) (funExt pos-path) module zag≡ where
    open module G = Container G renaming (Shape to T ; Pos to Q)

    shape-path : (∂s : Σ[ t ∈ T ] R ↪° Q t) → ∂[ counit G ] .Cart.shape (unit-shape (∂ G) ∂s) ≡ ∂s
    shape-path (t , f , _) = ΣPathP λ where
      .fst → refl′ t
      .snd → ↪°-≡ $ refl′ f

    pos-path : ∀ ∂s → ∂[ counit G ] .Cart.pos _ ∙ₑ (unit-pos (∂ G) ∂s) ≡ idEquiv (Q (∂s .fst) - ∂s .snd .fst)
    pos-path ∂s = invEquivPathP $ funExt λ where
      (t , ¬fib) → Complement≡ $ refl′ t

  is-natural-counit : (F G : Container ℓ ℓ) (f : Cart F G) → (counit F) ⋆ f ≡ ([ ∂[ f ] ]⊗ 𝕪 R) ⋆ counit G
  is-natural-counit F G f = Cart≡ refl $ funExt λ where
    ((s , f) , _) → invEquivPathP $ funExt λ where
      (inl p) → refl
      (inr r) → refl
