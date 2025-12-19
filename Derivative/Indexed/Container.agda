{-# OPTIONS --allow-unsolved-metas #-}
module Derivative.Indexed.Container where

open import Derivative.Prelude
open import Derivative.Basics.Embedding using (isEmbedding-Σ-map-snd ; isEmbeddingPostComp)
open import Derivative.Maybe
open import Derivative.Sum
open import Derivative.Basics.Decidable as Dec
open import Derivative.Isolated
open import Derivative.Remove

-- Re-export indexing types
open import Cubical.Data.Empty.Base renaming (⊥ to 𝟘 ; ⊥* to 𝟘*) public
open import Cubical.Data.Unit.Base renaming (Unit to 𝟙 ; tt to • ; tt* to •*) public -- • = \bub

open import Cubical.Data.Bool.Base using (Bool* ; true ; false)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv using (isPropIsEquiv)
open import Cubical.Foundations.Equiv.Properties
  using
    ( isEquiv[equivFunA≃B∘f]→isEquiv[f]
    ; isEquiv[f∘equivFunA≃B]→isEquiv[f]
    ; isEquivPostComp
    )
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Transport using (substEquiv ; subst2Equiv)
open import Cubical.Functions.Embedding using (isEmbedding ; isEquiv→isEmbedding)

record Container (ℓ : Level) (Ix : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor _◁_
  field
    Shape : Type ℓ
    Pos : Ix → Shape → Type ℓ

open Container

private
  variable
    ℓS ℓP ℓ : Level
    Ix : Type ℓ

-- Idices
tt° : 𝟙 °
tt° .fst = •
tt° .snd _ = yes refl

𝟚 : Type
𝟚 = Maybe 𝟙

pattern ₀ = inl •
{-# DISPLAY inl • = ₀ #-}
_ : 𝟚
_ = ₀

pattern ₁ = inr •*
{-# DISPLAY inr •* = ₁ #-}
_ : 𝟚
_ = ₁

₀° : 𝟚 °
₀° .fst = ₀
₀° .snd (inl _) = yes refl
₀° .snd (inr _) = no (inr≢inl ∘ sym)

₁° : 𝟚 °
₁° .fst = ₁
₁° .snd (inl _) = no inr≢inl
₁° .snd (inr (lift _)) = yes refl

record _⊸_ (F G : Container ℓ Ix) : Type ℓ where
  constructor [_⊸_]
  field
    shape : F .Shape → G .Shape
    pos : ∀ ix s → G .Pos ix (shape s) ≃ F .Pos ix s

infix 1 _⊸_

⊸-Σ-Iso : ∀ {F G : Container ℓ Ix} → Iso (F ⊸ G) (Σ[ shape ∈ (F .Shape → G .Shape) ] ∀ ix s → G .Pos ix (shape s) ≃ F .Pos ix s)
⊸-Σ-Iso {F} {G} = iso where
  iso : Iso _ _
  iso .Iso.fun [ shape ⊸ pos ] = shape , pos
  iso .Iso.inv (shape , pos) = [ shape ⊸ pos ]
  iso .Iso.rightInv _ = refl
  iso .Iso.leftInv _ = refl
  {-# INLINE iso #-}

⊸-Σ-equiv : ∀ {F G : Container ℓ Ix} → (F ⊸ G) ≃ (Σ[ shape ∈ (F .Shape → G .Shape) ] ∀ ix s → G .Pos ix (shape s) ≃ F .Pos ix s)
⊸-Σ-equiv = strictIsoToEquiv ⊸-Σ-Iso

⊸≡ : {F G : Container ℓ Ix}
  → {φ γ : F ⊸ G}
  → (p : φ ._⊸_.shape ≡ γ ._⊸_.shape)
  → (q : PathP (λ i → (ix : Ix) (s : F .Shape) → G .Pos ix (p i s) ≃ F .Pos ix s) (φ ._⊸_.pos) (γ ._⊸_.pos))
  → φ ≡ γ
⊸≡ p q i ._⊸_.shape = p i
⊸≡ p q i ._⊸_.pos = q i

⊸≡-ext : {F G : Container ℓ Ix}
  → {φ γ : F ⊸ G}
  → (p : φ ._⊸_.shape ≡ γ ._⊸_.shape)
  → (q : (ix : Ix) (s : F .Shape) → PathP (λ i → G .Pos ix (p i s) → F .Pos ix s) (equivFun $ φ ._⊸_.pos ix s) (equivFun $ γ ._⊸_.pos ix s))
  → φ ≡ γ
⊸≡-ext p q = ⊸≡ p (funExt λ ix → funExt λ s → equivPathP (q ix s))

_⋆_ : ∀ {F G H : Container ℓ Ix} → (F ⊸ G) → (G ⊸ H) → (F ⊸ H)
(f ⋆ g) ._⊸_.shape = g ._⊸_.shape ∘ f ._⊸_.shape
(f ⋆ g) ._⊸_.pos i s = g ._⊸_.pos i (f ._⊸_.shape s) ∙ₑ f ._⊸_.pos i s
infixl 9 _⋆_

⋆-assoc : ∀ {F G H K : Container ℓ Ix}
  → (f : F ⊸ G) (g : G ⊸ H) (h : H ⊸ K)
  → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
⋆-assoc f g h = ⊸≡-ext refl λ ix s → refl

id : (F : Container ℓ Ix) → F ⊸ F
id F ._⊸_.shape s = s
id F ._⊸_.pos s i = idEquiv _

_Π⊸_ : (F G : Container ℓ Ix) → Type ℓ
F Π⊸ G = (s : F .Shape) → Σ[ t ∈ G .Shape ] ∀ ix → G .Pos ix t ≃ F .Pos ix s

record Equiv (F G : Container ℓ Ix) : Type ℓ where
  constructor [_◁≃_]
  field
    shape : F .Shape ≃ G .Shape
    pos : ∀ ix s → G .Pos ix (equivFun shape s) ≃ F .Pos ix s

  as-⊸ : F ⊸ G
  as-⊸ ._⊸_.shape = equivFun shape
  as-⊸ ._⊸_.pos = pos

  inv : Equiv G F
  inv .shape = invEquiv shape
  inv .pos i t = invEquiv $ substEquiv (G .Pos i) (sym (secEq shape t)) ∙ₑ pos i (invEq shape t)

_⧟_ : (F G : Container ℓ Ix) → Type ℓ
_⧟_ = Equiv

_⋆ₑ_ : ∀ {F G H : Container ℓ Ix} → (F ⧟ G) → (G ⧟ H) → (F ⧟ H)
(f ⋆ₑ g) .Equiv.shape = f .Equiv.shape ∙ₑ g .Equiv.shape
(f ⋆ₑ g) .Equiv.pos i s = g .Equiv.pos i (equivFun (f .Equiv.shape) s) ∙ₑ f .Equiv.pos i s
infixl 9 _⋆ₑ_

isContainerEquiv : {F G : Container ℓ Ix} → F ⊸ G → Type _
isContainerEquiv f = isEquiv (_⊸_.shape f)

isContainerEquiv→Equiv : {F G : Container ℓ Ix} → (f : F ⊸ G) → isContainerEquiv f → F ⧟ G
isContainerEquiv→Equiv [ shape ⊸ pos ] is-equiv-f = [ shape , is-equiv-f ◁≃ pos ]

isPropIsContainerEquiv : {F G : Container ℓ Ix} {f : F ⊸ G} → isProp (isContainerEquiv f)
isPropIsContainerEquiv {f} = isPropIsEquiv (f ._⊸_.shape)

equivIsContainerEquiv : {F G : Container ℓ Ix} → (e : Equiv F G) → isContainerEquiv (Equiv.as-⊸ e)
equivIsContainerEquiv e = equivIsEquiv (e .Equiv.shape)

isContainerEquivId : (F : Container ℓ Ix) → isContainerEquiv (id F)
isContainerEquivId F = idIsEquiv _

isContainerEquivComp : {F G H : Container ℓ Ix}
  → (f : F ⊸ G)
  → (g : G ⊸ H)
  → isContainerEquiv f
  → isContainerEquiv g
  → isContainerEquiv (f ⋆ g)
isContainerEquivComp f g is-equiv-f is-equiv-g = equivIsEquiv ((_ , is-equiv-f) ∙ₑ (_ , is-equiv-g))

isContainerEquivCompLeft : {F G H : Container ℓ Ix}
  → (f : F ⊸ G)
  → (e : G ⧟ H)
  → isContainerEquiv (f ⋆ Equiv.as-⊸ e)
  → isContainerEquiv f
isContainerEquivCompLeft [ fₛ ⊸ _ ] [ eₛ ◁≃ _ ] = isEquiv[equivFunA≃B∘f]→isEquiv[f] fₛ eₛ

isContainerEquivCompLeft' : {F G H : Container ℓ Ix}
  → (f : F ⊸ G)
  → (e : G ⊸ H)
  → isContainerEquiv e
  → isContainerEquiv (f ⋆ e)
  → isContainerEquiv f
isContainerEquivCompLeft' f e is-equiv-e = isContainerEquivCompLeft f (isContainerEquiv→Equiv e is-equiv-e)

isContainerEquivCompRight : {F G H : Container ℓ Ix}
  → (e : F ⧟ G)
  → (f : G ⊸ H)
  → isContainerEquiv (Equiv.as-⊸ e ⋆ f)
  → isContainerEquiv f
isContainerEquivCompRight [ eₛ ◁≃ _ ] [ fₛ ⊸ _ ] = isEquiv[f∘equivFunA≃B]→isEquiv[f] fₛ eₛ

isContainerEquivCompRight' : {F G H : Container ℓ Ix}
  → (e : F ⊸ G)
  → (f : G ⊸ H)
  → isContainerEquiv e
  → isContainerEquiv (e ⋆ f)
  → isContainerEquiv f
isContainerEquivCompRight' e f is-equiv-e = isContainerEquivCompRight (isContainerEquiv→Equiv e is-equiv-e) f

isContainerEquivCompLeftRight : {F F′ G G′ : Container ℓ Ix}
  → (f : F ⧟ F′)
  → (g : G′ ⧟ G)
  → (e : F′ ⊸ G′)
  → isContainerEquiv (Equiv.as-⊸ f ⋆ e ⋆ Equiv.as-⊸ g)
  → isContainerEquiv e
isContainerEquivCompLeftRight f g e is-equiv-comp = isContainerEquivCompLeft e g is-equiv-comp' where
  is-equiv-comp' : isContainerEquiv (e ⋆ Equiv.as-⊸ g)
  is-equiv-comp' = isContainerEquivCompRight f (e ⋆ Equiv.as-⊸ g) is-equiv-comp

containerAdjointEquiv : {F G H : Container ℓ Ix}
  → (e : F ⧟ G)
  → (f₀ : F ⊸ H)
  → (f₁ : G ⊸ H)
  → (f₀ ≡ (Equiv.as-⊸ e) ⋆ f₁) ≃ (Equiv.as-⊸ (Equiv.inv e) ⋆ f₀ ≡ f₁)
containerAdjointEquiv e f₀ f₁ = {!  !}

isContainerEmbedding : {F G : Container ℓ Ix} → F ⊸ G → Type _
isContainerEmbedding f = isEmbedding (_⊸_.shape f)

isContainerEquiv→isContainerEmbedding : {F G : Container ℓ Ix} → {e : F ⊸ G}
  → isContainerEquiv e
  → isContainerEmbedding e
isContainerEquiv→isContainerEmbedding {e} = isEquiv→isEmbedding

module _ where
  private
    variable
      F G H : Container ℓ Ix

  _⊸⟨_⟩_ : (F : Container ℓ Ix) → (F ⊸ G) → (G ⊸ H) → (F ⊸ H)
  _⊸⟨_⟩_ {G} {H} F f g = _⋆_ {F = F} {G = G} {H = H} f g

  _⧟⟨_⟩_ : (F : Container ℓ Ix) → (Equiv F G) → (G ⊸ H) → (F ⊸ H)
  _⧟⟨_⟩_ {G} {H} F e g = _⋆_ {F = F} {G = G} {H = H} (Equiv.as-⊸ e) g

  _⊸≃⟨_⟩_ : (F : Container ℓ Ix) → (Equiv F G) → (G ⊸ H) → (F ⊸ H)
  _⊸≃⟨_⟩_ = _⧟⟨_⟩_
  {-# WARNING_ON_USAGE _⊸≃⟨_⟩_ "DEPRECATED" #-}

  _⊸∎ : (F : Container ℓ Ix) → F ⊸ F
  F ⊸∎ = id F
  {-# INLINE _⊸∎ #-}

  infixr 0 _⊸⟨_⟩_
  infixr 0 _⧟⟨_⟩_
  infixr 0 _⊸≃⟨_⟩_
  infix 1 _⊸∎

_⟨_⟩[_] : (F : Container ℓ Ix) (i : Ix °) (G : Container ℓ (Ix - i)) → Container ℓ (Ix - i)
_⟨_⟩[_] {Ix} F (i , i≟_) G = shape ◁ pos module ⟨-⟩[-] where
  shape : Type _
  shape = Σ[ s ∈ F .Shape ] (F .Pos i s → G .Shape)

  pos-dec : (j : Ix) → i ≢ j → Dec (i ≡ j) → shape → Type _
  pos-dec j i≢j (yes i≡j) _ = ex-falso $ i≢j i≡j
  pos-dec j i≢j (no  _) (s , f) = F .Pos j s ⊎ (Σ[ p ∈ F .Pos i s ] G .Pos (j , i≢j) (f p))

  pos : Ix ∖ i → shape → Type _
  pos (j , i≢j) = pos-dec j i≢j (i≟ j)


_[_] : (F : Container ℓ (Maybe Ix)) (G : Container ℓ Ix) → Container ℓ Ix
F [ G ] = shape ◁ pos module [-] where
  shape : Type _
  shape = Σ[ s ∈ F .Shape ] (F .Pos nothing s → G .Shape)

  pos : _ → shape → Type _
  pos ix (s , f) = F .Pos (just ix) s ⊎ (Σ[ p ∈ F .Pos nothing s ] G .Pos ix (f p))

private
  sanity : (F : Container ℓ (Maybe Ix)) (G : Container ℓ Ix)
    → ∀ (ix : Maybe Ix - nothing°) s → (F [ G ]) .Pos (remove-nothing ix) s ≃ (F ⟨ nothing° ⟩[ subst (Container ℓ) (sym $ ua removeNothingEquiv) G ]) .Pos ix s
  sanity F G (just ix , _) (s , f) = ⊎-right-≃ (Σ-cong-equiv-snd λ p → subst2Equiv (G .Pos) (sym (transportRefl ix)) (sym (transportRefl (f p))))
  sanity F G (nothing , ₁≢₁) = ex-falso $ ₁≢₁ refl

⊸-intro : {F G : Container ℓ Ix}
  → ((s : F .Shape) → Σ[ t ∈ G .Shape ] ∀ i → G .Pos i t ≃ F .Pos i s)
  → F ⊸ G
⊸-intro f = [ fst ∘ f ⊸ (λ i s → f s .snd i) ]

[-]-map : (F : Container ℓ (Maybe Ix)) {G G′ : Container ℓ Ix}
  → G ⊸ G′
  → (F [ G ]) ⊸ (F [ G′ ])
[-]-map F {G} {G′} φ = [ shape ⊸ pos ] module [-]-map where
  module φ = _⊸_ φ

  shape : Σ[ s ∈ Shape F ] (Pos F nothing s → Shape G) → Σ[ s ∈ Shape F ] (Pos F nothing s → Shape G′)
  shape = Σ-map-snd (λ s → φ.shape ∘_)

  pos : ∀ i ((s , f) : Σ[ s ∈ Shape F ] (Pos F nothing s → Shape G))
    →
      F .Pos (just i) s ⊎ (Σ[ p ∈ F .Pos nothing s ] G′ .Pos i (φ.shape (f p)))
        ≃
      F .Pos (just i) s ⊎ (Σ[ p ∈ F .Pos nothing s ] G .Pos i (f p))
  pos i (s , f) = ⊎-right-≃ $ Σ-cong-equiv-snd λ p → φ.pos i (f p)

isEquiv-[-]-map : (F : Container ℓ (Maybe Ix)) {G G′ : Container ℓ Ix}
  → (φ : G ⊸ G′)
  → isContainerEquiv φ
  → isContainerEquiv ([-]-map F φ)
isEquiv-[-]-map F φ is-equiv-φ = is-equiv-shape where
  module φ = _⊸_ φ
  open [-]-map F φ using (shape)

  is-equiv-postcomp : (s : Shape F) → isEquiv (φ.shape ∘_)
  is-equiv-postcomp s = isEquivPostComp (φ.shape , is-equiv-φ)

  is-equiv-shape : isEquiv shape
  is-equiv-shape = isEquiv-Σ-map-snd is-equiv-postcomp

isEmbedding-[-]-map : (F : Container ℓ (Maybe Ix)) {G G′ : Container ℓ Ix}
  → (φ : G ⊸ G′)
  → isContainerEmbedding φ
  → isContainerEmbedding ([-]-map F φ)
isEmbedding-[-]-map F {G} {G′} φ is-emb-φ = is-emb-shape where
  module φ = _⊸_ φ
  open [-]-map F φ using (shape)

  is-emb-postcomp : (s : Shape F) → isEmbedding (φ.shape ∘_)
  is-emb-postcomp s = isEmbeddingPostComp φ.shape is-emb-φ

  is-emb-shape : isEmbedding shape
  is-emb-shape = isEmbedding-Σ-map-snd is-emb-postcomp

_⊗_ : (F G : Container ℓ Ix) → Container ℓ Ix
_⊗_ F G = shape ◁ pos module ⊗ where
  shape : Type _
  shape = F .Shape × G .Shape

  pos : _ → shape → Type _
  pos ix (s , t) = F .Pos ix s ⊎ G .Pos ix t

_⊕_ : (F G : Container ℓ Ix) → Container ℓ Ix
_⊕_ F G = shape ◁ pos module ⊕ where
  shape : Type _
  shape = F .Shape ⊎ G .Shape

  pos : _ → shape → Type _
  pos ix (inl s) = F .Pos ix s
  pos ix (inr t) = G .Pos ix t

-- Lifting a container to one with an aditional index
↑ : Container ℓ Ix → Container ℓ (Maybe Ix)
↑ F .Shape = F .Shape
↑ F .Pos (just i) = F .Pos i
↑ F .Pos nothing _ = 𝟘*

-- Projection onto the 0ᵗʰ and 1ˢᵗ variable
π₀ : Container _ 𝟚
π₀ .Shape = 𝟙
π₀ .Pos ₀ _ = 𝟙
π₀ .Pos ₁ _ = 𝟘

π₁ : Container _ 𝟚
π₁ .Shape = 𝟙
π₁ .Pos ₀ _ = 𝟘
π₁ .Pos ₁ _ = 𝟙

-- This is well-behaved for isolated (i : Ix):
π : (i : Ix) → Container ℓ Ix
π i .Shape = Lift 𝟙
π i .Pos j _ = i ≡ j

π° : {Ix : Type} → (i : Ix °) → Container ℓ-zero Ix
π° (i , i≟_) .Shape = 𝟙
π° (i , i≟_) .Pos j _ = Dec→Type (i≟ j)

_ : π° ₀° ≡ π₀
_ = cong (𝟙 ◁_) $ funExt λ where
  ₀ → refl
  ₁ → refl
