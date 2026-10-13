{-# OPTIONS --safe #-}
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
  ∂ F = ∂F where
    open module F = Container F renaming (Shape to S ; Pos to P)

    S′ : Type _
    S′ = Σ[ s ∈ S ] (R ↪° P s)

    P′ : S′ → Type _
    P′ (s , f , _) = P s - f

    ∂F : Container _ _
    ∂F .Container.Shape = S′
    ∂F .Container.Pos = P′
    {-# INLINE ∂F #-}

  ∂[_] : {F G : Container ℓ ℓ} → F ⊸ G → (∂ F) ⊸ (∂ G)
  ∂[_] {F} {G} φ = ∂f module ∂[-] where
    open Container
    open _⊸_ φ renaming (shape to f ; pos to u)

    shape : (Σ[ s ∈ F .Shape ] R ↪° F .Pos s) → (Σ[ t ∈ G .Shape ] R ↪° G .Pos t)
    shape (s , _) .fst = f s
    shape (s , p) .snd = dec-emb-postcomp-equiv p $ invEquiv (u s)

    pos : (s : F .Shape) (p : R → F .Pos s) → (G .Pos (f s) - (p ⨟ invEq (u s))) ≃ (F .Pos s - p)
    pos s p = complementSubstEquiv' p (u s)

    ∂f : (∂ F) ⊸ (∂ G)
    ∂f ._⊸_.shape = shape
    ∂f ._⊸_.pos ∂s = pos (∂s .fst) (∂s .snd .fst)
    {-# INLINE ∂f #-}

  module _ (F : Container ℓ ℓ) where
    open _⊸_
    private
      open module F = Container F renaming (Shape to S ; Pos to P)

    unit-shape : S → Σ[ (s , _) ∈ S × 𝟙* {ℓ} ] (R ↪° (P s ⊎ R))
    unit-shape s .fst .fst = s
    unit-shape s .fst .snd = •
    unit-shape s .snd = inr-dec-emb

    unit-pos : (s : S) → ((P s ⊎ R) - inr) ≃ P s
    unit-pos s = invEquiv sum-inr-remove-equiv

    unit : F ⊸ (∂ (F ⊗ 𝕪 R))
    unit .shape = unit-shape
    unit .pos = unit-pos

  is-natural-unit : (F G : Container ℓ ℓ) (f : F ⊸ G) → (unit F) ⋆ ∂[ [ f ]⊗ 𝕪 R ] ≡ f ⋆ unit G
  is-natural-unit F G f = ⊸≡ (funExt λ s → ΣPathP (refl′ (f ._⊸_.shape s , •) , ↪°-≡ (refl′ inr)))
    $ funExt λ s → equivExt λ where
      (inl q , _) → refl′ $ equivFun (f ._⊸_.pos s) q
      (inr r , ¬inr≡inr) → ex-falso $ ¬inr≡inr (r , refl)

  module _ (G : Container ℓ ℓ) where
    open _⊸_
    private
      open module G = Container G renaming (Shape to T ; Pos to Q)

    counit-shape : (Σ[ t ∈ T ] (R ↪° Q t)) × 𝟙* {ℓ} → T
    counit-shape ((t , _ , _) , _) = t

    counit-pos : ∀ (t : T) (f : R ↪° Q t)  → Q t ≃ ((Q t - f .fst) ⊎ R)
    counit-pos t f = invEquiv (remove-sum-left-equiv f)

    counit : (∂ G ⊗ 𝕪 R) ⊸ G
    counit .shape = counit-shape
    counit .pos ((t , f) , _) = counit-pos t f

  zig : (F : Container ℓ ℓ) → (F ⊗ 𝕪 R) ⊸ (F ⊗ 𝕪 R)
  zig F =
    (F ⊗ 𝕪 R)           ⊸⟨ [ unit F ]⊗ 𝕪 R ⟩
    (∂ (F ⊗ 𝕪 R) ⊗ 𝕪 R) ⊸⟨ counit (F ⊗ 𝕪 R) ⟩
    (F ⊗ 𝕪 R)           ⊸∎

  zig≡ : (F : Container ℓ ℓ) → ([ unit F ]⊗ (𝕪 R)) ⋆ counit (F ⊗ 𝕪 R) ≡ id (F ⊗ 𝕪 R)
  zig≡ F = ⊸≡ refl (funExt pos-path) module zig≡ where
    pos-path : ∀ s → (counit-pos (F ⊗ 𝕪 R) s inr-dec-emb) ∙ₑ ⊎-left-≃ (unit-pos F (s .fst)) ≡ idEquiv _
    pos-path s = equivExt λ where
      (inl p) → refl′ $ inl p
      (inr r) → refl′ $ inr r

  zag≡ : (G : Container ℓ ℓ) → unit (∂ G) ⋆ ∂[ counit G ] ≡ id (∂ G)
  zag≡ G = ⊸≡ (funExt shape-path) (funExt pos-path) module zag≡ where
    open module G = Container G renaming (Shape to T ; Pos to Q)
    open _⊸_ using (shape ; pos)

    shape-path : (∂s : Σ[ t ∈ T ] R ↪° Q t) → ∂[ counit G ] .shape (unit (∂ G) .shape ∂s) ≡ ∂s
    shape-path (t , f , _) = ΣPathP (refl′ t , ↪°-≡ (refl′ f))

    pos-path : ∀ ∂s → ∂[ counit G ] .pos (unit (∂ G) .shape ∂s) ∙ₑ (unit (∂ G) .pos ∂s) ≡ idEquiv (Q (∂s .fst) - ∂s .snd .fst)
    pos-path ∂s = invEquivPathP $ funExt λ where
      (t , ¬fib) → Complement≡ $ refl′ t

  is-natural-counit : (F G : Container ℓ ℓ) (f : F ⊸ G) → (counit F) ⋆ f ≡ ([ ∂[ f ] ]⊗ 𝕪 R) ⋆ counit G
  is-natural-counit F G f = ⊸≡ refl $ funExt λ where
    ((s , f) , _) → invEquivPathP $ funExt λ where
      (inl p) → refl
      (inr r) → refl

module _ where
  open import Derivative.Derivative using () renaming (∂ to ∂¹)
  open import Derivative.Basics.Unit using (isContr-𝟙*)

  firstDerivativeEquiv : (F : Container ℓ-zero ℓ-zero) → Equiv (∂¹ F) (∂ 𝟙 F)
  firstDerivativeEquiv _ .Equiv.shape = Σ-cong-equiv-snd λ s → Isolated≃DecEmbUnit
  firstDerivativeEquiv F@(S ◁ P) .Equiv.pos (s , p , p-isolated) = pos-equiv where
    pos-equiv : (P s - const p) ≃ (P s ∖ p)
    pos-equiv = Σ-cong-equiv-snd λ p → preCompEquiv {C = ⊥} $ invEquiv $ Σ-contractFst isContr-𝟙*
