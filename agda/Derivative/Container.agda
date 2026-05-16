{-# OPTIONS --safe #-}
module Derivative.Container where

open import Derivative.Prelude
import      Derivative.Basics.Decidable as Dec
import      Derivative.Basics.Maybe as Maybe
open import Derivative.Basics.Sum as Sum using (_⊎_)

open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma.Base

record Container (ℓS ℓP : Level) : Type (ℓ-suc (ℓ-max ℓS ℓP)) where
  -- no-eta-equality
  constructor _◁_
  field
    Shape : Type ℓS
    Pos : Shape → Type ℓP

private
  variable
    ℓS ℓP ℓ : Level

Container-syntax : (S : Type ℓS) → (P : S → Type ℓP) → Container ℓS ℓP
Container-syntax = _◁_

syntax Container-syntax S (λ s → P) = [ s ∈ S ]◁ P

open Container

isTruncatedContainer : (n k : HLevel) → Container ℓS ℓP → Type _
isTruncatedContainer n k (S ◁ P) = isOfHLevel n S × ∀ s → isOfHLevel k (P s)

isSetContainer : Container ℓS ℓP → Type _
isSetContainer = isTruncatedContainer 2 2

TruncatedContainer : (n k : HLevel) (ℓS ℓP : Level) → Type (ℓ-suc (ℓ-max ℓS ℓP))
TruncatedContainer n k ℓS ℓP = Σ (Container ℓS ℓP) (isTruncatedContainer n k)

SetContainer : (ℓS ℓP : Level) → Type (ℓ-suc (ℓ-max ℓS ℓP))
SetContainer = TruncatedContainer 2 2

isDiscreteContainer : Container ℓS ℓP → Type _
isDiscreteContainer F = ∀ s → Dec.Discrete (F .Pos s)

DiscreteContainer : (ℓS ℓP : Level) → Type _
DiscreteContainer ℓS ℓP = Σ[ F ∈ Container ℓS ℓP ] isDiscreteContainer F

_⊗_ : (F G : Container ℓS ℓP) → Container _ _
(F ⊗ G) .Shape = F .Shape × G .Shape
(F ⊗ G) .Pos x = F .Pos (x .fst) ⊎ G .Pos (x .snd)
infix 11 _⊗_

Id : Container ℓS ℓP
Id .Shape = 𝟙*
Id .Pos = const 𝟙*

_⊗Id : Container ℓS ℓP → Container ℓS ℓP
F ⊗Id = F ⊗ Id

_⊕_ : (F G : Container ℓS ℓP) → Container _ _
(F ⊕ G) .Shape = F .Shape ⊎ G .Shape
(F ⊕ G) .Pos (Sum.inl s) = F .Pos s
(F ⊕ G) .Pos (Sum.inr t) = G .Pos t
infix 10 _⊕_

Const : (S : Type ℓ) → Container ℓ ℓ
Const S .Shape = S
Const S .Pos _ = 𝟘*

One : (ℓ : Level) → Container ℓ ℓ
One ℓ = Const 𝟙*

record Cart {ℓS ℓT ℓP ℓQ} (F : Container ℓS ℓP) (G : Container ℓT ℓQ) : Type (ℓ-max (ℓ-max ℓS ℓP) (ℓ-max ℓT ℓQ)) where
  constructor [_◁_]
  field
    shape : F .Shape → G .Shape
    pos : ∀ s → G .Pos (shape s) ≃ F .Pos s

open Cart

unquoteDecl Cart-Σ-Iso = declareRecordIsoΣ Cart-Σ-Iso (quote Cart)

Cart-Σ-equiv : ∀ {ℓS ℓT ℓP ℓQ} {F : Container ℓS ℓP} {G : Container ℓT ℓQ}
  → Cart F G ≃ (Σ[ fₛₕ ∈ (F .Shape → G .Shape) ] ∀ s → G .Pos (fₛₕ s) ≃ F .Pos s)
Cart-Σ-equiv = isoToEquiv Cart-Σ-Iso

Cart≡ : {F G : Container ℓS ℓP}
  → {f g : Cart F G}
  → (p : f .shape ≡ g .shape)
  → (q : PathP (λ i → ∀ s → G .Pos (p i s) ≃ F .Pos s) (f .pos) (g .pos))
  → f ≡ g
Cart≡ p q i .shape = p i
Cart≡ p q i .pos = q i

Cart≡Equiv : {F G : Container ℓS ℓP}
  → (f g : Cart F G)
  → (Σ[ p ∈ f .shape ≡ g .shape ] (PathP (λ i → ∀ s → G .Pos (p i s) ≃ F .Pos s) (f .pos) (g .pos))) ≃ (f ≡ g)
Cart≡Equiv f g = strictIsoToEquiv iso module Cart≡Equiv where
  iso : Iso _ _
  iso .Iso.fun = uncurry Cart≡
  iso .Iso.inv p .fst = cong shape p
  iso .Iso.inv p .snd = cong pos p
  iso .Iso.rightInv _ = refl
  iso .Iso.leftInv _ = refl

_⋆_ : ∀ {F G H : Container ℓS ℓP} → Cart F G → Cart G H → Cart F H
(f ⋆ g) .shape = g .shape ∘ f .shape
(f ⋆ g) .pos s = g .pos (f .shape s) ∙ₑ f .pos s
-- {-# INJECTIVE_FOR_INFERENCE _⋆_ #-}

id : (F : Container ℓS ℓP) → Cart F F
id F .shape s = s
id F .pos s = idEquiv _

TruncatedCart : {n k : HLevel} → (F G : TruncatedContainer n k ℓS ℓP) → Type _
TruncatedCart F G = Cart (F .fst) (G .fst)
{-# INJECTIVE_FOR_INFERENCE TruncatedCart #-}

SetCart : (F G : TruncatedContainer 2 2 ℓS ℓP) → Type _
SetCart = TruncatedCart {n = 2} {k = 2}

isOfHLevelCart : (n : HLevel) → {F G : TruncatedContainer n n ℓS ℓP} → isOfHLevel n (TruncatedCart F G)
isOfHLevelCart n {F = _ , _ , trunc-pos-F} {G = _ , trunc-shape-G , trunc-pos-G} = isOfHLevelRetractFromIso n Cart-Σ-Iso
  $ isOfHLevelΣ n
    (isOfHLevelΠ n λ _ → trunc-shape-G)
    λ f → isOfHLevelΠ n λ s → isOfHLevel≃ n (trunc-pos-G (f s)) (trunc-pos-F s)

module CartReasoning where
  private
    variable
      F G H : Container ℓS ℓP

  _⊸⟨_⟩_ : (F : Container ℓS ℓP) {G H : Container ℓS ℓP} → Cart F G → Cart G H → Cart F H
  _⊸⟨_⟩_ F {G} {H} f g = _⋆_ {F = F} {G = G} {H = H} f g

  _⊸∎ : (F : Container ℓS ℓP) → Cart F F
  F ⊸∎ = id F
  {-# INLINE _⊸∎ #-}

  infixr 0 _⊸⟨_⟩_
  infix 1 _⊸∎

open CartReasoning public

[_]⊗Id : {F G : Container ℓS ℓP} → Cart F G → Cart (F ⊗Id) (G ⊗Id)
[_]⊗Id {F} {G} f .shape s = f .shape (s .fst) , _
[_]⊗Id {F} {G} f .pos s = Sum.⊎-left-≃ (f .pos (s .fst))

record Equiv (F G : Container ℓS ℓP) : Type (ℓ-max ℓS ℓP) where
  constructor [_◁≃_]
  field
    shape : F .Shape ≃ G .Shape
    pos : ∀ s → G .Pos (equivFun shape s) ≃ F .Pos s

Equiv→Cart : {F G : Container ℓS ℓP} → Equiv F G → Cart F G
Equiv→Cart [ shape ◁≃ pos ] .shape = equivFun shape
Equiv→Cart [ shape ◁≃ pos ] .pos = pos

_⋆ₑ_ : ∀ {F G H : Container ℓS ℓP} → Equiv F G → Equiv G H → Equiv F H
(f ⋆ₑ g) .Equiv.shape = f .Equiv.shape ∙ₑ g .Equiv.shape
(f ⋆ₑ g) .Equiv.pos s = g .Equiv.pos (equivFun (f .Equiv.shape) s) ∙ₑ f .Equiv.pos s

idₑ : (F : Container ℓS ℓP) → Equiv F F
idₑ F .Equiv.shape = idEquiv _
idₑ F .Equiv.pos _ = idEquiv _

-- TODO: Rename to Equiv-shape and Equiv-pos
Equiv-fst : ∀ {S S′ : Type ℓS} {P : S′ → Type ℓP}
  → (e : S ≃ S′)
  → Equiv (S ◁ (P ∘ equivFun e)) (S′ ◁ P)
Equiv-fst {S} {P} e .Equiv.shape = e
Equiv-fst {S} {P} e .Equiv.pos s = idEquiv (P (equivFun e s))

Equiv-snd : ∀ {S : Type ℓS} {P P′ : S → Type ℓP}
  → (e : ∀ s → P′ s ≃ P s)
  → Equiv (S ◁ P) (S ◁ P′)
Equiv-snd {S} e .Equiv.shape = idEquiv S
Equiv-snd {S} e .Equiv.pos = e

Equiv-inv : {F G : Container ℓS ℓ} → Equiv F G → Equiv G F
Equiv-inv {F} {G} [ shape ◁≃ pos ] .Equiv.shape = invEquiv shape
Equiv-inv {F} {G} [ shape ◁≃ pos ] .Equiv.pos t = invEquiv $ substEquiv (G .Pos) (sym (secEq shape t)) ∙ₑ pos (invEq shape t)

module EquivReasoning where
  private
    variable
      F G H : Container ℓS ℓP

  _⊸≃⟨_⟩_ : (F : Container ℓS ℓP) → Equiv F G → Equiv G H → Equiv F H
  _⊸≃⟨_⟩_ {G} {H} F f g = _⋆ₑ_ {F = F} {G = G} {H = H} f g

  _⊸≃∎ : (F : Container ℓS ℓP) → Equiv F F
  F ⊸≃∎ = idₑ F
  {-# INLINE _⊸≃∎ #-}

  _⊸≃⟨⟩_ : (F : Container ℓS ℓP) → Equiv F G → Equiv F G
  F ⊸≃⟨⟩ e = e

  infixr 0 _⊸≃⟨_⟩_
  infixr 0 _⊸≃⟨⟩_
  infix 1 _⊸≃∎

open EquivReasoning public

_[_] : (F G : Container ℓ ℓ) → Container ℓ ℓ
(F [ G ]) .Shape = Σ[ s ∈ F .Shape ] (F .Pos s → G .Shape)
(F [ G ]) .Pos (s , f) = Σ[ p ∈ F .Pos s ] G .Pos (f p)
