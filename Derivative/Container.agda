module Derivative.Container where

open import Derivative.Prelude
import      Derivative.Maybe as Maybe

open import Cubical.Data.Empty as Empty using (⊥*)
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sum.Base as Sum using (_⊎_)
import      Cubical.Data.Unit as Unit

record Container (ℓS ℓP : Level) : Type (ℓ-suc (ℓ-max ℓS ℓP)) where
  no-eta-equality
  constructor _◁_
  field
    Shape : Type ℓS
    Pos : Shape → Type ℓP

private
  variable
    ℓS ℓP ℓ : Level

open Container

_⊗_ : (F G : Container ℓS ℓP) → Container _ _
(F ⊗ G) .Shape = F .Shape × G .Shape
(F ⊗ G) .Pos x = F .Pos (x .fst) ⊎ G .Pos (x .snd)
infix 11 _⊗_

Id : Container ℓS ℓP
Id .Shape = ⊤ _
Id .Pos = const $ ⊤ _

_⊗Id : Container ℓS ℓP → Container ℓS ℓP
F ⊗Id = F ⊗ Id

_⊕_ : (F G : Container ℓS ℓP) → Container _ _
(F ⊕ G) .Shape = F .Shape ⊎ G .Shape
(F ⊕ G) .Pos (Sum.inl s) = F .Pos s
(F ⊕ G) .Pos (Sum.inr t) = G .Pos t
infix 10 _⊕_

Zero : Container ℓS ℓP
Zero .Shape = Unit.Unit*
Zero .Pos _ = ⊥*

record Cart (F G : Container ℓS ℓP) : Type (ℓ-max ℓS ℓP) where
  constructor [_◁_]
  field
    shape : F .Shape → G .Shape
    pos : ∀ s → G .Pos (shape s) ≃ F .Pos s

open Cart

Cart≡ : {F G : Container ℓS ℓP}
  → {f g : Cart F G}
  → (p : f .shape ≡ g .shape)
  → (q : PathP (λ i → ∀ s → G .Pos (p i s) ≃ F .Pos s) (f .pos) (g .pos))
  → f ≡ g
Cart≡ p q i .shape = p i
Cart≡ p q i .pos = q i

_⋆_ : ∀ {F G H : Container ℓS ℓP} → Cart F G → Cart G H → Cart F H
(f ⋆ g) .shape = g .shape ∘ f .shape
(f ⋆ g) .pos s = g .pos (f .shape s) ∙ₑ f .pos s
-- {-# INJECTIVE_FOR_INFERENCE _⋆_ #-}

id : (F : Container ℓS ℓP) → Cart F F
id F .shape s = s
id F .pos s = idEquiv _

module _ where
  private
    variable
      F G H : Container ℓS ℓP

  _⊸⟨_⟩_ : (F : Container ℓS ℓP) → Cart F G → Cart G H → Cart F H
  _⊸⟨_⟩_ {G} {H} F f g = _⋆_ {F = F} {G = G} {H = H} f g

  _⊸∎ : (F : Container ℓS ℓP) → Cart F F
  F ⊸∎ = id F
  {-# INLINE _⊸∎ #-}

  infixr 0 _⊸⟨_⟩_
  infix 1 _⊸∎

[_]⊗Id : {F G : Container ℓS ℓP} → Cart F G → Cart (F ⊗Id) (G ⊗Id)
[_]⊗Id {F} {G} f .shape s = f .shape (s .fst) , _
[_]⊗Id {F} {G} f .pos s = Maybe.map-equiv (f .pos (s .fst))

record Equiv (F G : Container ℓS ℓP) : Type (ℓ-max ℓS ℓP) where
  constructor [_◁≃_]
  field
    shape : F .Shape ≃ G .Shape
    pos : ∀ s → G .Pos (equivFun shape s) ≃ F .Pos s

_[_] : (F G : Container ℓ ℓ) → Container ℓ ℓ
(F [ G ]) .Shape = Σ[ s ∈ F .Shape ] (F .Pos s → G .Shape)
(F [ G ]) .Pos (s , f) = Σ[ p ∈ F .Pos s ] G .Pos (f p)
