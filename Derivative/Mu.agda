{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Derivative.Mu where

open import Derivative.Prelude
open import Derivative.Maybe
open import Derivative.Sum
open import Derivative.Decidable as Dec
open import Derivative.Isolated
open import Derivative.Remove

open import Cubical.Data.Unit.Base using (tt) renaming (Unit to 𝟙)
open import Cubical.Data.Bool.Base using (Bool* ; true ; false)
open import Cubical.Data.Sigma
open import Cubical.Data.W.W
open import Cubical.Data.Empty as Empty using (⊥*) renaming (⊥ to 𝟘)
open import Cubical.Foundations.Transport using (substEquiv ; subst⁻)

private
  pattern true* = lift true
  pattern false* = lift false

tt° : 𝟙 °
tt° .fst = tt
tt° .snd tt = yes refl

𝟚 = Maybe 𝟙

-- ₀ : 𝟚
pattern ₀ = inl tt

-- ₁ : 𝟚
pattern ₁ = inr (lift tt)

₀° : 𝟚 °
₀° .fst = ₀
₀° .snd (inl tt) = yes refl
₀° .snd (inr _) = no (inr≢inl ∘ sym)

₁° : 𝟚 °
₁° .fst = ₁
₁° .snd (inl _) = no inr≢inl
₁° .snd (inr (lift tt)) = yes refl

record Container (ℓ : Level) (Ix : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor _◁_
  field
    Shape : Type ℓ
    Pos : Ix → Shape → Type ℓ

private
  variable
    ℓS ℓP ℓ : Level
    Ix : Type ℓ

  _-_ : (Ix : Type ℓ) (ix : Ix °) → Type ℓ
  Ix - ix = Ix ∖ (ix .fst)

  module _ (S : Type ℓS) (P₀ P₁ : S → Type ℓP) where
    data Wᴰ : W S P₁ → Type (ℓ-max ℓS ℓP) where
      top : {s : S} {f : P₁ s → W S P₁}
        → (p₀ : P₀ s)
        → Wᴰ (sup-W s f)
      below : {s : S} {f : P₁ s → W S P₁}
        → (p₁ : P₁ s)
        → (wᴰ : Wᴰ (f p₁))
        → Wᴰ (sup-W s f)

    Wᴰ-equiv : ∀ s f → Wᴰ (sup-W s f) ≃ P₀ s ⊎ (Σ[ p₁ ∈ P₁ s ] (Wᴰ (f p₁)))
    Wᴰ-equiv s f = isoToEquiv iso module Wᴰ-equiv where
      iso : Iso _ _
      iso .Iso.fun (top p₀) = inl p₀
      iso .Iso.fun (below p₁ w) = inr (p₁ , w)
      iso .Iso.inv (inl p₀) = top p₀
      iso .Iso.inv (inr (p₁ , w)) = below p₁ w
      iso .Iso.rightInv (inl _) = refl
      iso .Iso.rightInv (inr _) = refl
      iso .Iso.leftInv (top p₀) = refl
      iso .Iso.leftInv (below p₁ a) = refl

    Wᴰ-isolated-equiv : ∀ s f → (Wᴰ (sup-W s f)) ° ≃ (P₀ s °) ⊎ ((Σ[ p₁ ∈ P₁ s ] (Wᴰ (f p₁))) °)
    Wᴰ-isolated-equiv s f =
      (Wᴰ (sup-W s f)) °
        ≃⟨ IsolatedSubstEquiv (Wᴰ-equiv s f) ⟩
      (P₀ s ⊎ (Σ[ p₁ ∈ P₁ s ] (Wᴰ (f p₁)))) °
        ≃⟨ IsolatedSumEquiv ⟩
      (P₀ s °) ⊎ ((Σ[ p₁ ∈ P₁ s ] (Wᴰ (f p₁))) °)
        ≃∎

    Wᴰ-remove-top : ∀ s f p₀ → isIsolated p₀ → Wᴰ (sup-W s f) ∖ top p₀ ≃ (P₀ s ∖ p₀) ⊎ (Σ[ p₁ ∈ P₁ s ] (Wᴰ (f p₁)))
    Wᴰ-remove-top s f p₀ is-isolated-p₀ =
      Wᴰ (sup-W s f) ∖ top p₀
        ≃⟨ RemoveRespectEquiv (inl p₀) (Wᴰ-equiv s f) ⟩
      (P₀ s ⊎ (Σ[ p₁ ∈ P₁ s ] (Wᴰ (f p₁)))) ∖ inl p₀
        ≃⟨ invEquiv (remove-left-equiv is-isolated-p₀) ⟩
      (P₀ s ∖ p₀) ⊎ (Σ[ p₁ ∈ P₁ s ] (Wᴰ (f p₁)))
        ≃∎

    Wᴰ-remove-below : ∀ s f p₁ (wᴰ : Wᴰ (f p₁))
      → isIsolated p₁
      → isIsolated wᴰ
      → Wᴰ (sup-W s f) ∖ below p₁ wᴰ ≃ (P₀ s) ⊎ ((Σ[ (p , _) ∈ P₁ s ∖ p₁ ] Wᴰ (f p)) ⊎ (Wᴰ (f p₁) ∖ wᴰ))
    Wᴰ-remove-below s f p₁ wᴰ is-isolated-p₁ is-isolated-wᴰ =
      Wᴰ (sup-W s f) ∖ below p₁ wᴰ
        ≃⟨ RemoveRespectEquiv (inr (p₁ , wᴰ)) (Wᴰ-equiv s f) ⟩
      (P₀ s ⊎ (Σ[ p₁ ∈ P₁ s ] Wᴰ (f p₁))) ∖ inr (p₁ , wᴰ)
        ≃⟨ invEquiv (remove-right-equiv is-isolated-p₁-wᴰ) ⟩
      (P₀ s) ⊎ ((Σ[ p₁ ∈ P₁ s ] Wᴰ (f p₁)) ∖ (p₁ , wᴰ))
        ≃⟨ ⊎-right-≃ $ invEquiv $ isIsolatedFst→Σ-remove-equiv is-isolated-p₁ ⟩
      (P₀ s) ⊎ ((Σ[ (p , _) ∈ P₁ s ∖ p₁ ] Wᴰ (f p)) ⊎ (Wᴰ (f p₁) ∖ wᴰ))
        ≃∎
        where
          is-isolated-p₁-wᴰ : isIsolated {A = Σ[ p₁ ∈ P₁ s ] (Wᴰ (f p₁))} (p₁ , wᴰ)
          is-isolated-p₁-wᴰ = isIsolatedΣ is-isolated-p₁ is-isolated-wᴰ

  module _ {S : Type ℓS} {P : S → Type ℓP} where
    out-W : W S P → (Σ[ s ∈ S ] (P s → W S P))
    out-W (sup-W s f) = s , f

    in-W : (Σ[ s ∈ S ] (P s → W S P)) → W S P
    in-W = uncurry sup-W

    in-W≃ : (Σ[ s ∈ S ] (P s → W S P)) ≃ W S P
    in-W≃ = isoToEquiv iso module in-W≃ where
      iso : Iso (Σ[ s ∈ S ] (P s → W S P)) (W S P)
      iso .Iso.fun = in-W
      iso .Iso.inv = out-W
      iso .Iso.rightInv (sup-W s f) = refl
      iso .Iso.leftInv _ = refl

  module _ {ℓS ℓT ℓP ℓQ}
    {S : Type ℓS} {T : Type ℓT}
    {P : S → Type ℓP} {Q : T → Type ℓQ}
    where
    W-map : (f : S → T) (fᴰ : ∀ {s} → Q (f s) → P s) → W S P → W T Q
    W-map f fᴰ (sup-W s w) = sup-W (f s) λ q → W-map f fᴰ (w (fᴰ q))

  module _ {ℓS ℓT ℓP ℓQ}
    {S : Type ℓS} {T : Type ℓT}
    {P : S → Type ℓP} {Q : T → Type ℓQ}
    where
    W-subst-Iso :
      ∀ (i : Iso S T)
      → (iᴰ : ∀ {s} → Iso (Q (Iso.fun i s)) (P s))
      → Iso (W S P) (W T Q)
    W-subst-Iso i iᴰ .Iso.fun = W-map (Iso.fun i) (Iso.fun iᴰ)
    W-subst-Iso i iᴰ .Iso.inv = W-map (Iso.inv i) λ {s} p → subst Q (Iso.rightInv i s) $ Iso.inv iᴰ p
    W-subst-Iso i iᴰ .Iso.rightInv (sup-W s x) = {! !}
    W-subst-Iso i iᴰ .Iso.leftInv = {! !}

    W-subst-equiv :
      ∀ (e : S ≃ T)
      → (eᴰ : ∀ s → Q (equivFun e s) ≃ P s)
      → W S P ≃ W T Q
    W-subst-equiv e eᴰ .fst = W-map (equivFun e) (equivFun (eᴰ _))
    W-subst-equiv e eᴰ .snd .equiv-proof (sup-W t z) = isOfHLevelRespectEquiv 0 fiber-equiv {! !} where
      fiber-equiv : (Σ[ (t′ , p) ∈ singl t ] singlP (λ i → Q (p i) → W T Q) z) ≃ fiber (W-map (equivFun e) (equivFun (eᴰ _))) (sup-W t z)
      fiber-equiv =
        {! !}
          ≃⟨ {! !} ⟩
        Σ[ xx ∈ W _ _ ] W-map (equivFun e) (equivFun (eᴰ _)) xx ≡ sup-W t z
          ≃∎

μ : (F : Container ℓ (Maybe Ix)) → Container ℓ Ix
μ {ℓ} {Ix} F = shape ◁ pos module μ where
  open Container F renaming (Shape to S ; Pos to P)

  shape : Type ℓ
  shape = W S (P nothing)

  pos : Ix → shape → Type ℓ
  pos ix = Wᴰ S (P (just ix)) (P nothing)

μ' : (ix : Ix) → (F : Container ℓ Ix) → Container ℓ (Ix ∖ ix)
μ' {Ix} i F = shape ◁ pos where
  open Container F renaming (Shape to S ; Pos to P)

  shape : Type _
  shape = W S (P i)

  pos : (Ix ∖ i) → shape → Type _
  pos (j , _) = Wᴰ S (P j) (P i)

open Container

record _⊸_ (F G : Container ℓ Ix) : Type ℓ where
  constructor [_⊸_]
  field
    shape : F .Shape → G .Shape
    pos : ∀ ix s → G .Pos ix (shape s) ≃ F .Pos ix s

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
-- {-# INJECTIVE_FOR_INFERENCE _⋆_ #-}

id : (F : Container ℓ Ix) → F ⊸ F
id F ._⊸_.shape s = s
id F ._⊸_.pos s i = idEquiv _

module _ where
  private
    variable
      F G H : Container ℓ Ix

  _⊸⟨_⟩_ : (F : Container ℓ Ix) → (F ⊸ G) → (G ⊸ H) → (F ⊸ H)
  _⊸⟨_⟩_ {G} {H} F f g = _⋆_ {F = F} {G = G} {H = H} f g

  _⊸∎ : (F : Container ℓ Ix) → F ⊸ F
  F ⊸∎ = id F
  {-# INLINE _⊸∎ #-}

  infixr 0 _⊸⟨_⟩_
  infix 1 _⊸∎

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

_∘[_]_ : (F : Container ℓ Ix) → (i : Ix) → (G : Container ℓ (Ix ∖ i)) → Container ℓ (Ix ∖ i)
_∘[_]_ {Ix} F i G = shape ◁ pos module ∘[-] where
  shape : Type _
  shape = Σ[ s ∈ F .Shape ] (F .Pos i s → G .Shape)

  pos : (Ix ∖ i) → shape → Type _
  pos j (s , f) = F .Pos (j .fst) s ⊎ (Σ[ p ∈ F .Pos i s ] G .Pos j (f p))
  
_[_]' : ∀ {Ix Jx : Type ℓ} → (F : Container ℓ (Ix ⊎ Jx)) (G : Jx → Container ℓ Ix) → Container ℓ Ix
_[_]' {Ix} {Jx} F G = shape ◁ pos module [-]' where
  open Container F renaming (Shape to S ; Pos to P)
  module _ (j : Jx) where
    open Container (G j) renaming (Shape to T ; Pos to Q) public
  
  Pᴵ : Ix → S → Type _
  Pᴵ i = P (inl i)

  Pᴶ : Jx → S → Type _
  Pᴶ j = P (inr j)

  shape : Type _
  shape = Σ[ s ∈ S ] (∀ {j} → Pᴶ j s → T j)

  pos : _ → shape → Type _
  pos i (s , f) = Pᴵ i s ⊎ (Σ[ j ∈ Jx ] Σ[ p ∈ Pᴶ j s ] Q j i (f p))
  
_[_] : (F : Container ℓ (Maybe Ix)) (G : Container ℓ Ix) → Container ℓ Ix
F [ G ] = shape ◁ pos module [-] where
  shape : Type _
  shape = Σ[ s ∈ F .Shape ] (F .Pos nothing s → G .Shape)

  pos : _ → shape → Type _
  pos ix (s , f) = F .Pos (just ix) s ⊎ (Σ[ p ∈ F .Pos nothing s ] G .Pos ix (f p))
  
μ-in : (F : Container ℓ (Maybe Ix)) → Equiv (F [ μ F ]) (μ F)
μ-in F = [ shape ◁≃ pos ] where
  open Container F renaming (Shape to S ; Pos to P)

  shape : Shape (F [ μ F ]) ≃ Shape (μ F)
  shape = in-W≃

  pos : ∀ ix w* → Pos (μ F) ix (in-W w*) ≃ Pos (F [ μ F ]) ix w*
  pos ix (s , ws) = Wᴰ-equiv S (P (just ix)) (P nothing) s ws

μ-in' : (i : Ix) → (F : Container ℓ Ix) → Equiv (F ∘[ i ] (μ' i F)) (μ' i F)
μ-in' i F = [ shape ◁≃ pos ] where
  open Container F renaming (Shape to S ; Pos to P)

  shape : Shape (F ∘[ i ] (μ' i F)) ≃ Shape (μ' i F)
  shape = in-W≃

  pos : ∀ j w* → Pos (μ' i F) j (in-W w*) ≃ Pos (F ∘[ i ] (μ' i F)) j w*
  pos (j , _) (s , ws) = Wᴰ-equiv S (P j) (P i) s ws

⊸-intro : {F G : Container ℓ Ix}
  → ((s : F .Shape) → Σ[ t ∈ G .Shape ] ∀ i → G .Pos i t ≃ F .Pos i s)
  → F ⊸ G
⊸-intro f = [ fst ∘ f ⊸ (λ i s → f s .snd i) ]

μ-rec : (F : Container ℓ (Maybe Ix))
  → (G : Container ℓ Ix)
  → (F [ G ]) ⊸ G
  → μ F ⊸ G
μ-rec F G φ = [ shape ⊸ pos ] where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  module φ = _⊸_ φ

  shape : W S (P ₁) → T
  shape (sup-W s f) = φ.shape (s , λ p → shape (f p))

  pos : ∀ i → (s : W S (P ₁)) → Q i (shape s) ≃ Pos (μ F) i s
  pos i (sup-W s f) =
    Q i (φ.shape (s , shape ∘ f))
      ≃⟨ φ.pos i (s , shape ∘ f) ⟩
    (P (just i) s ⊎ (Σ[ p ∈ P nothing s ] Q i (shape (f p))))
      ≃⟨ ⊎-right-≃ (Σ-cong-equiv-snd λ p → pos i (f p)) ⟩
    (P (just i) s ⊎ (Σ[ p ∈ P nothing s ] Pos (μ F) i (f p)))
      ≃⟨ invEquiv (Wᴰ-equiv S (P (just i)) (P nothing) s f) ⟩
    Wᴰ S (P (just i)) (P nothing) (sup-W s f)
      ≃∎

[-]-map : (F : Container ℓ (Maybe Ix)) {G G′ : Container ℓ Ix}
  → G ⊸ G′
  → (F [ G ]) ⊸ (F [ G′ ])
[-]-map F {G} {G′} φ = [ shape ⊸ pos ] where
  module φ = _⊸_ φ

  shape : Σ[ s ∈ Shape F ] (Pos F ₁ s → Shape G) → Σ[ s ∈ Shape F ] (Pos F ₁ s → Shape G′)
  shape = Σ-map-snd (λ s → φ.shape ∘_)

  pos : ∀ i ((s , f) : Σ[ s ∈ Shape F ] (Pos F ₁ s → Shape G))
    →
      F .Pos (just i) s ⊎ (Σ[ p ∈ F .Pos nothing s ] G′ .Pos i (φ.shape (f p)))
        ≃
      F .Pos (just i) s ⊎ (Σ[ p ∈ F .Pos nothing s ] G .Pos i (f p))
  pos i (s , f) = ⊎-right-≃ $ Σ-cong-equiv-snd λ p → φ.pos i (f p)

μ-rec-unique : (F : Container ℓ (Maybe Ix))
  → (G : Container ℓ Ix)
  → (α : (F [ G ]) ⊸ G)
  → isContr (Σ[ α* ∈ μ F ⊸ G ] Equiv.as-⊸ (μ-in F) ⋆ α* ≡ [-]-map F α* ⋆ α )
μ-rec-unique F G α .fst .fst = μ-rec F G α
μ-rec-unique F G α .fst .snd = ⊸≡-ext refl λ ix s → funExt λ { xx → {! !} }
μ-rec-unique F G α .snd (α* , p) = ΣPathP ({! !} , {! !})

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

∑ : {J : Type ℓ} (F : J → Container ℓ Ix) → Container ℓ Ix
∑ {J} F .Shape = Σ[ j ∈ J ] F j .Shape
∑ {J} F .Pos ix (j , s) = F j .Pos ix s

syntax ∑ {J = J} (λ j → F) = ∑[ j ∈ J ] F

∑-Bool-equiv : (F : Bool* → Container ℓ Ix) → Equiv (∑ F) (F false* ⊕ F true*)
∑-Bool-equiv F = [ shape ◁≃ pos ] module Σ-Bool-equiv where
  shape : Σ Bool* (Shape ∘ F) ≃ Shape (F false*) ⊎ Shape (F true*)
  shape = isoToEquiv λ where
    .Iso.fun (true* , s) → inr s
    .Iso.fun (false* , s) → inl s
    .Iso.inv (inl s) → false* , s
    .Iso.inv (inr s) → true* , s
    .Iso.leftInv (true* , s) → refl
    .Iso.leftInv (false* , s) → refl
    .Iso.rightInv (inl s) → refl
    .Iso.rightInv (inr s) → refl

  pos : ∀ ix → (s* : Σ Bool* (Shape ∘ F)) → Pos (F false* ⊕ F true*) ix (equivFun shape s*) ≃ Pos (F (s* .fst)) ix (s* .snd)
  pos ix (true* , s) = idEquiv _
  pos ix (false* , s) = idEquiv _

∂ : (i : Ix °) → (F : Container ℓ Ix) → Container ℓ Ix
∂ {ℓ} {Ix} (i , i≟_) F = shape ◁ pos module ∂ where
  open Container F renaming (Shape to S ; Pos to P)
  shape : Type ℓ
  shape = Σ[ s ∈ S ] ((P i s) °)

  pos-dec : (j : Ix) → Dec (i ≡ j) → shape → Type _
  pos-dec j (yes i≡j) (s , p , _) = P i s ∖ p
  pos-dec j (no  i≢j) (s , p , _) = P j s

  pos : Ix → shape → Type _
  pos j = pos-dec j (i≟ j)

∂-map : (i : Ix °) → {F G : Container ℓ Ix} → (F ⊸ G) → (∂ i F ⊸ ∂ i G)
∂-map (i , i≟_) {F} {G} φ = [ shape ⊸ pos ] where
  module φ = _⊸_ φ

  shape : Σ _ _ → Σ _ _
  shape = Σ-map φ.shape λ s → invEq (IsolatedSubstEquiv (φ.pos i s))

  pos-dec : ∀ j → (i≟j : Dec (i ≡ j)) → ∀ s → ∂.pos-dec i i≟_ G j i≟j (shape s) ≃ ∂.pos-dec i i≟_ F j i≟j s
  pos-dec j (yes i≡j) (s , p , _) = RemoveRespectEquiv p (φ.pos i s)
  pos-dec j (no ¬i≡j) (s , _) = φ.pos j s

  pos : ∀ j s → _ ≃ _
  pos j = pos-dec j (i≟ j)

{-
chain-rule' : ∀ {Ix : Type ℓ}
  → (i : Ix) (j : (Ix ∖ i) °)
  → (F : Container ℓ Ix)
  → (G : Container ℓ (Ix ∖ i))
  → (∑[ k ∈ Ix ° ] ((∂ k F ∘[ i ] G) ⊗ ∂ j G)) ⊸ ∂ j (F ∘[ i ] G)
chain-rule' {Ix} i (j≢@(j , i≢j) , j≟_) F G = [ shape ⊸ {! !} ] module chain-rule' where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  shape :
    (Σ[ k ∈ Ix ° ] (Σ[ sp ∈ (Σ[ s ∈ S ] P (k .fst) s °) ] (∂.pos (k .fst) (k .snd) F i sp → T)) × (Σ[ t ∈ T ] (Q j≢ t °)))
      →
    Σ[ (s , f) ∈ Σ[ s ∈ S ] (P i s → T) ] ((P j s ⊎ (Σ[ p ∈ P i s ] Q j≢ (f p))) °)
  shape = {! !}
-}

binary-chain-rule :
  ∀ (F : Container _ 𝟚)
  → (G : Container _ 𝟙)
  → ((∂ ₀° F [ G ]) ⊕ ((∂ ₁° F [ G ]) ⊗ ∂ tt° G)) ⊸ ∂ tt° (F [ G ])
binary-chain-rule F G = [ shape ⊸ pos ] module binary-chain-rule where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  shape-equiv :
    ((Σ[ (s , _) ∈ Σ[ s ∈ S ] P ₀ s ° ] (P ₁ s → T)) ⊎ ((Σ[ (s , p , _) ∈ Σ[ s ∈ S ] P ₁ s ° ] (P ₁ s ∖ p → T)) × (Σ[ t ∈ T ] Q tt t °)))
      ≃
    (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P ₁ s → T) ] (P ₀ s °) ⊎ (Σ[ (p , _) ∈ P ₁ s ° ] Q tt (f p) °))
  shape-equiv =
    ((Σ[ (s , _) ∈ Σ[ s ∈ S ] P ₀ s ° ] (P ₁ s → T)) ⊎ ((Σ[ (s , p , _) ∈ Σ[ s ∈ S ] P ₁ s ° ] (P ₁ s ∖ p → T)) × (Σ[ t ∈ T ] Q tt t °)))
      ≃⟨ ⊎-equiv Σ-assoc-≃ shuffle-right ⟩
    ((Σ[ s ∈ S ] P ₀ s ° × (P ₁ s → T)) ⊎ (Σ[ s ∈ S ] Σ[ (p , _) ∈ P ₁ s ° ] Σ[ (_ , t) ∈ (P ₁ s ∖ p → T) × T ] (Q tt t °)))
      ≃⟨ invEquiv Σ-⊎-snd-≃ ⟩
    Σ[ s ∈ S ] (P ₀ s ° × (P ₁ s → T)) ⊎ (Σ[ (p , _) ∈ P ₁ s ° ] Σ[ (_ , t) ∈ (P ₁ s ∖ p → T) × T ] (Q tt t °))
      ≃⟨ Σ-cong-equiv-snd (λ s → ⊎-right-≃ $ Σ-cong-equiv-snd λ p° → invEquiv $ Σ-cong-equiv-fst $ unstitchEquiv p°) ⟩
    Σ[ s ∈ S ] (P ₀ s ° × (P ₁ s → T)) ⊎ (Σ[ (p , _) ∈ P ₁ s ° ] Σ[ f ∈ (P ₁ s → T) ] (Q tt (f p) °))
      ≃⟨ Σ-cong-equiv-snd (λ s → ⊎-equiv Σ-swap-≃ Σ-swap-fst-≃) ⟩
    Σ[ s ∈ S ] ((P ₁ s → T) × P ₀ s °) ⊎ (Σ[ f ∈ (P ₁ s → T) ] Σ[ (p , _) ∈ P ₁ s ° ] (Q tt (f p) °))
      ≃⟨ Σ-cong-equiv-snd (λ s → invEquiv Σ-⊎-snd-≃) ⟩
    Σ[ s ∈ S ] Σ[ f ∈ (P ₁ s → T) ] ((P ₀ s °) ⊎ (Σ[ (p , _) ∈ P ₁ s ° ] (Q tt (f p) °)))
      ≃⟨ invEquiv Σ-assoc-≃ ⟩
    Σ[ (s , f) ∈ Σ[ s ∈ S ] (P ₁ s → T) ] (((P ₀ s °) ⊎ (Σ[ (p , _) ∈ P ₁ s ° ] Q tt (f p) °)))
      ≃∎
      where
        shuffle-right : _ ≃ _
        shuffle-right = strictEquiv
          (λ (((s , p°) , f) , (t , q)) → (s , p° , (f , t) , q))
          (λ (s , p° , (f , t) , q) → (((s , p°) , f) , (t , q)))

  shape :
    (Σ[ (s , _) ∈ Σ[ s ∈ S ] P ₀ s ° ] (P ₁ s → T)) ⊎ ((Σ[ (s , p , _) ∈ Σ[ s ∈ S ] P ₁ s ° ] (P ₁ s ∖ p → T)) × (Σ[ t ∈ T ] Q tt t °))
      →
    Σ[ (s , f) ∈ Σ[ s ∈ S ] (P ₁ s → T) ] (P ₀ s ⊎ (Σ[ p ∈ P ₁ s ] Q tt (f p))) °
  shape =
    _ →≃⟨ shape-equiv ⟩
    Σ[ (s , f) ∈ Σ[ s ∈ S ] (P ₁ s → T) ] (P ₀ s °) ⊎ (Σ[ (p , _) ∈ P ₁ s ° ] Q tt (f p) °)
      →⟨ Σ-map-snd (λ { (s , f) → ⊎-map-right (Σ-isolate (P ₁ s) (Q tt ∘ f)) }) ⟩
    Σ[ (s , f) ∈ Σ[ s ∈ S ] (P ₁ s → T) ] (P ₀ s °) ⊎ ((Σ[ p ∈ P ₁ s ] Q tt (f p)) °)
      →≃⟨ Σ-cong-equiv-snd (λ { (s , f) → invEquiv IsolatedSumEquiv }) ⟩
    _ →∎

  pos₀ : (s : S) (p°@(p₀ , _) : P ₀ s °) → (f : P ₁ s → T)
    →
      (P ₀ s ⊎ (Σ[ p ∈ P ₁ s ] (Q tt (f p)))) ∖ inl p₀
        ≃
      ((P ₀ s ∖ p₀) ⊎ (Σ[ p ∈ P ₁ s ] (Q tt (f p))))
  pos₀ s p° f = invEquiv (remove-left-equiv (p° .snd))

  pos₁ : (s : S) (p°@(p₁ , _) : P ₁ s °) → (f : P ₁ s ∖ p₁ → T) → (t : T) → (q°@(q , _) : Q tt t °)
     →
      (P ₀ s ⊎ (Σ[ p ∈ P ₁ s ] Q tt (stitch p° (f , t) p))) ∖ Sum.inr (p₁ , _)
        ≃
      ((P ₀ s ⊎ (Σ[ p ∈ (P ₁ s) ∖ p₁ ] Q tt (f p))) ⊎ (Q tt t ∖ q))
  pos₁ s p°@(p₁ , is-isolated-p₁) f t q°@(q , is-isolated-q)
    using pq ← (p₁ , subst⁻ (Q tt) (stitch-β p° f) q)
    using is-isolated-pq ← isIsolatedΣ is-isolated-p₁ (isIsolatedSubst (Q tt) (sym $ stitch-β p° f) is-isolated-q)
    =
      (P ₀ s ⊎ (Σ[ p ∈ P ₁ s ] Q tt (stitch p° (f , t) p))) ∖ Sum.inr pq
        ≃⟨ invEquiv (remove-right-equiv is-isolated-pq) ⟩
      (P ₀ s ⊎ ((Σ[ p ∈ P ₁ s ] Q tt (stitch p° (f , t) p)) ∖ pq))
        ≃⟨ ⊎-right-≃ $ invEquiv $ isIsolatedFst→Σ-remove-equiv is-isolated-p₁ ⟩
      (P ₀ s ⊎ ((Σ[ (p , _) ∈ P ₁ s ∖ p₁ ] Q tt (stitch p° (f , t) p)) ⊎ (Q tt (stitch p° (f , t) p₁) ∖ pq .snd)))
        ≃⟨ ⊎-right-≃ $ ⊎-equiv (Σ-cong-equiv-snd subst-Q₀) subst-Q₁ ⟩
      (P ₀ s ⊎ ((Σ[ p ∈ (P ₁ s) ∖ p₁ ] Q tt (f p)) ⊎ (Q tt t ∖ q)))
        ≃⟨ invEquiv ⊎-assoc-≃ ⟩
      ((P ₀ s ⊎ (Σ[ p ∈ (P ₁ s) ∖ p₁ ] Q tt (f p))) ⊎ (Q tt t ∖ q))
        ≃∎
        where
          subst-Q₀ : (p : P ₁ s ∖ p₁) → Q tt (stitch p° (f , t) (p .fst)) ≃ Q tt (f p)
          subst-Q₀ p = substEquiv (Q tt) (stitch-β' p° f p)

          subst-Q₁ : (Q tt (stitch p° (f , t) p₁) ∖ pq .snd) ≃ (Q tt t ∖ q)
          subst-Q₁ = invEquiv $ RemoveRespectEquiv' q $ substEquiv (Q tt) (sym $ stitch-β p° f)

  pos : (ix : 𝟙)
    → (s : Shape ((∂ ₀° F [ G ]) ⊕ ((∂ ₁° F [ G ]) ⊗ ∂ tt° G)))
    →
      Pos (∂ tt° (F [ G ])) ix (shape s)
        ≃
      Pos ((∂ ₀° F [ G ]) ⊕ ((∂ ₁° F [ G ]) ⊗ ∂ tt° G)) ix s
  pos tt (inl ((s , p°) , f)) = pos₀ s p° f
  pos tt (inr (((s , p°) , f) , t , q°)) = pos₁ s p° f t q°

{-
chain-rule : ∀ {Ix : Type ℓ}
  → (F : Container ℓ (Maybe Ix))
  → (G : Container ℓ Ix)
  → (j : Ix °)
  → (∑[ i ∈ Ix ° ] ((∂ (just° i) F [ G ]) ⊗ ∂ j G)) ⊸ ∂ j (F [ G ])
chain-rule {Ix} F G (j , j≟_) = [ shape ⊸ {! !} ] module chain-rule where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)
  
  shape≃ :
    (Σ[ (i , _) ∈ Ix ° ] (Σ[ (s , _) ∈ (Σ[ s ∈ S ] P (just i) s °) ] (P nothing s → T)) × (Σ[ t ∈ T ] (Q j t °)))
      ≃
    (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P nothing s → T) ] (P (just j) s ⊎ (Σ[ (p , _) ∈ P nothing s ° ] Q j (f p) °)))
  shape≃ =
    (Σ[ (i , _) ∈ Ix ° ] (Σ[ (s , _) ∈ (Σ[ s ∈ S ] P (just i) s °) ] (P nothing s → T)) × (Σ[ t ∈ T ] (Q j t °)))
      ≃⟨ {! !} ⟩
    (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P nothing s → T) ] (P (just j) s ⊎ (Σ[ (p , _) ∈ P nothing s ° ] Q j (f p) °)))
      ≃∎

  shape :
    (Σ[ (i , _) ∈ Ix ° ] (Σ[ (s , _) ∈ (Σ[ s ∈ S ] P (just i) s °) ] (P nothing s → T)) × (Σ[ t ∈ T ] (Q j t °)))
      →
    Σ[ (s , f) ∈ Σ[ s ∈ S ] (P nothing s → T) ] ((P (just j) s ⊎ (Σ[ p ∈ P nothing s ] Q j (f p))) °)
  shape ((i , _) , ((s , p°) , f) , t , q°) .fst .fst = s
  shape ((i , _) , ((s , p°) , f) , t , q°) .fst .snd = f
  shape ((i , _) , ((s , p°) , f) , t , q°) .snd .fst = {! !}
  shape ((i , _) , ((s , p°) , f) , t , q°) .snd .snd = {! !}

chain-rule'' : ∀ {Ix : Type ℓ}
  → (F : Container ℓ (Maybe Ix))
  → (G : Container ℓ Ix)
  → (j : Ix °)
  → (∑[ i ∈ Ix ° ] ((∂ (just° i) F [ G ]) ⊗ ∂ j G)) ⊸ ∂ j (F [ G ])
chain-rule'' {Ix} F G (j , j≟_) = [ shape ⊸ {! !} ] module chain-rule'' where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)
  
  shape≃ :
    (Σ[ (i , _) ∈ Ix ° ] (Σ[ (s , _) ∈ (Σ[ s ∈ S ] P (just i) s °) ] (P nothing s → T)) × (Σ[ t ∈ T ] (Q j t °)))
      ≃
    (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P nothing s → T) ] (P (just j) s ⊎ (Σ[ (p , _) ∈ P nothing s ° ] Q j (f p) °)))
  shape≃ =
    (Σ[ (i , _) ∈ Ix ° ] (Σ[ (s , _) ∈ (Σ[ s ∈ S ] P (just i) s °) ] (P nothing s → T)) × (Σ[ t ∈ T ] (Q j t °)))
      ≃⟨ {! !} ⟩
    (Σ[ (s , f) ∈ Σ[ s ∈ S ] (P nothing s → T) ] (P (just j) s ⊎ (Σ[ (p , _) ∈ P nothing s ° ] Q j (f p) °)))
      ≃∎

  shape :
    (Σ[ (i , _) ∈ Ix ° ] (Σ[ (s , _) ∈ (Σ[ s ∈ S ] P (just i) s °) ] (P nothing s → T)) × (Σ[ t ∈ T ] (Q j t °)))
      →
    Σ[ (s , f) ∈ Σ[ s ∈ S ] (P nothing s → T) ] ((P (just j) s ⊎ (Σ[ p ∈ P nothing s ] Q j (f p))) °)
  shape ((i , _) , ((s , p°) , f) , t , q°) .fst .fst = s
  shape ((i , _) , ((s , p°) , f) , t , q°) .fst .snd = f
  shape ((i , _) , ((s , p°) , f) , t , q°) .snd .fst = {! !}
  shape ((i , _) , ((s , p°) , f) , t , q°) .snd .snd = {! !}
-}

↑ : Container ℓ Ix → Container ℓ (Maybe Ix)
↑ F .Shape = F .Shape
↑ F .Pos (just i) = F .Pos i
↑ F .Pos nothing _ = ⊥*

Id : Container ℓ-zero Ix
Id .Shape = 𝟙
Id .Pos i _ = 𝟙

μ-rule : ∀ (F : Container _ 𝟚) →
  μ ((↑ (∂ ₀° F [ μ F ])) ⊕ ((↑ (∂ ₁° F [ μ F ])) ⊗ Id))
    ⊸
  ∂ tt° (μ F)
μ-rule F = μ-rec F′ _ goal where
  open Container F renaming (Shape to S ; Pos to P)

  F′ : Container _ 𝟚
  F′ = (↑ (∂ ₀° F [ μ F ])) ⊕ ((↑ (∂ ₁° F [ μ F ])) ⊗ Id)

  F″ : Container _ 𝟙
  F″ = (∂ ₀° F [ μ F ]) ⊕ ((∂ ₁° F [ μ F ]) ⊗ ∂ tt° (μ F))

  shape-Iso : Iso (Shape (F′ [ ∂ tt° (μ F) ])) (Shape F″)
  shape-Iso .Iso.fun (inl ∂₀s , _) = inl ∂₀s
  shape-Iso .Iso.fun (inr (∂₁s , _) , f) = inr (∂₁s , f (inr tt))
  shape-Iso .Iso.inv (inl ∂₀s) = inl ∂₀s , λ ()
  shape-Iso .Iso.inv (inr (∂₁s , ∂μs)) = inr (∂₁s , tt) , λ { (inr tt) → ∂μs }
  shape-Iso .Iso.rightInv (inl ∂₀s) = refl
  shape-Iso .Iso.rightInv (inr (∂₁s , ∂μs)) = refl
  shape-Iso .Iso.leftInv (inl ∂₀s , 0→∂μs) = ΣPathP (refl , λ { i () })
  shape-Iso .Iso.leftInv (inr (∂₁s , tt) , f) = ΣPathP (refl , funExt λ { (inr tt) → refl′ (f _) })

  shape : Shape (F′ [ ∂ tt° (μ F) ]) ≃ Shape F″
  shape = isoToEquiv shape-Iso

  pos₀ : (s : S) (p° : P ₀ s °) (μs : P ₁ s → Shape (μ F)) (f : ⊥* → Shape (∂ tt° (μ F)))
    →
      (P ₀ s - p°) ⊎ (Σ[ p ∈ P ₁ s ] Wᴰ S (P ₀) (P ₁) (μs p))
        ≃
      ((P ₀ s - p°) ⊎ (Σ[ p ∈ P ₁ s ] Wᴰ S (P ₀) (P ₁) (μs p))) ⊎ (Σ[ x ∈ ⊥* ] (Pos (μ F) tt (f x .fst)) ∖ f x .snd .fst)
  pos₀ s p° μs f = ⊎-empty-right (λ ())

  pos : (i : 𝟙) → (s : Shape $ F′ [ ∂ tt° (μ F) ]) → Pos F″ i (equivFun shape s) ≃ Pos (F′ [ ∂ tt° (μ F) ]) i s
  pos _ (just ((s , p°) , μs) , f) = pos₀ s p° μs f
  pos _ (inr ∂₁s , f) = {! !}

  goal : (F′ [ ∂ tt° (μ F) ]) ⊸ ∂ tt° (μ F)
  goal =
    (F′ [ ∂ tt° (μ F) ])
      ⊸⟨ Equiv.as-⊸ [ shape ◁≃ pos ] ⟩
    ((∂ ₀° F [ μ F ]) ⊕ ((∂ ₁° F [ μ F ]) ⊗ ∂ tt° (μ F)))
      ⊸⟨ binary-chain-rule F (μ F) ⟩
    ∂ tt° (F [ μ F ])
      ⊸⟨ ∂-map tt° (Equiv.as-⊸ (μ-in F)) ⟩
    ∂ tt° (μ F)
      ⊸∎
