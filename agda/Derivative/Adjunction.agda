{-# OPTIONS --safe #-}
module Derivative.Adjunction where

open import Derivative.Prelude
open import Derivative.Container
open import Derivative.Basics.Decidable
open import Derivative.Basics.Maybe
open import Derivative.Derivative
open import Derivative.Isolated
open import Derivative.Remove

open import Cubical.Data.Sum.Base as Sum using (_⊎_ ; inl ; inr)

private
  variable
    ℓ : Level

open Container
open Cart

module _ (F : Container ℓ ℓ) where
  open Container F renaming (Shape to S ; Pos to P)

  unit-shape : S → Σ[ s ∈ S × 𝟙* {ℓ} ] (P (s .fst) ⊎ 𝟙*) °
  unit-shape s .fst = s , _
  unit-shape s .snd = nothing°

  unit-pos : (s : S) → Maybe (P s) ∖ nothing ≃ P s
  unit-pos s = removeNothingEquiv

  unit : Cart F (∂ (F ⊗Id))
  unit .shape = unit-shape
  unit .pos = unit-pos

module _ (G : Container ℓ ℓ) where
  open Container G renaming (Shape to T ; Pos to Q)
  counit-shape : (Σ[ t ∈ T ] (Q t) °) × 𝟙* {ℓ} → T
  counit-shape ((t , _ , _) , _) = t

  counit-pos : ∀ (t : T) (q : (Q t)) → isIsolated q → Q t ≃ ((Q t ∖ q) ⊎ 𝟙*)
  counit-pos t q isolated-q = unreplace-isolated-equiv q isolated-q

  counit : Cart (∂ G ⊗Id) G
  counit .shape = counit-shape
  counit .pos ((t , q , isolated-q) , _) = counit-pos t q isolated-q

is-natural-unit : (F G : Container ℓ ℓ) (f : Cart F G) → unit F ⋆ ∂[ [ f ]⊗Id ] ≡ f ⋆ unit G
is-natural-unit F G f = Cart≡ (funExt λ s → ΣPathP (refl′ (f .shape s , •) , Isolated≡ refl))
  $ funExt λ s → equivExt λ where
    (just q , _) → refl′ (equivFun (f .pos s) q)
    (nothing , nothing≢nothing) → ex-falso $ nothing≢nothing refl

is-natural-counit : (F G : Container ℓ ℓ) (f : Cart F G) → [ ∂[ f ] ]⊗Id ⋆ counit G ≡ counit F ⋆ f
is-natural-counit F G f = Cart≡ refl $ funExt λ { ((s , p°) , _) → equivExt (goal s p°) }
  where
    opaque
      unfolding isIsolatedRespectEquiv

      goal : (s : F .Shape) (p°@(p₀ , p₀≟_) : F .Pos s °)
        → (let (q₀ , q₀≟_) = ∂[ f ] .shape (s , p°) .snd)
        → (q : G .Pos (f .shape s))
        →
          equivFun (maybe-equiv (∂[ f ] .pos (s , p°))) (unreplace q₀ q₀≟_ q)
            ≡
          unreplace p₀ p₀≟_ (equivFun (f .pos s) q)
      goal s p°@(p₀ , p₀≟_) q
        using p ← equivFun (f .pos s) q
        with (p₀≟ p)
      ... | (yes p₀≡p) = refl
      ... | (no ¬p₀≡p) = cong {B = λ _ → Maybe (F .Pos s ∖ _)} just (Remove≡ $ refl′ p)

zig : (F : Container ℓ ℓ) → Cart (F ⊗Id) (F ⊗Id)
zig F =
  F ⊗Id           ⊸⟨ [ unit F ]⊗Id ⟩
  (∂ (F ⊗Id) ⊗Id) ⊸⟨ counit (F ⊗Id) ⟩
  F ⊗Id           ⊸∎

zig≡ : (F : Container ℓ ℓ) → [ unit F ]⊗Id ⋆ counit (F ⊗Id) ≡ id (F ⊗Id)
zig≡ F = Cart≡ refl (funExt pos-path) module zig≡ where
  opaque
    unfolding isIsolatedRespectEquiv

    pos-path : ∀ s → (counit-pos (F ⊗Id) s nothing isIsolatedNothing) ∙ₑ maybe-equiv (unit-pos F (s .fst)) ≡ idEquiv _
    pos-path s = equivExt λ where
      (just p) → refl′ (just p)
      nothing → refl′ nothing

zag : (G : Container ℓ ℓ) → Cart (∂ G) (∂ G)
zag G =
  ∂ G         ⊸⟨ unit (∂ G) ⟩
  ∂ (∂ G ⊗Id) ⊸⟨ ∂[ counit G ] ⟩
  ∂ G         ⊸∎

zag≡ : (G : Container ℓ ℓ) → unit (∂ G) ⋆ ∂[ counit G ] ≡ id (∂ G)
zag≡ G = Cart≡ (funExt shape-path) (funExt λ ∂s → equivExt (pos-path ∂s)) module zag≡ where
  shape-path : (s : Σ[ s ∈ Shape G ] Pos G s °) → ∂[ counit G ] .shape (unit-shape (∂ G) s) ≡ s
  shape-path (s , (p₀ , _)) = ΣPathP λ where
    .fst → refl′ s
    .snd → Isolated≡ $ refl′ p₀

  opaque
    pos-path : (∂s : ∂ G .Shape) (∂p : ∂ G .Pos ∂s) → remove-nothing (equivFun (∂[ counit G ] .pos (unit-shape (∂ G) ∂s)) ∂p) ≡ ∂p
    pos-path (s , p°@(p₀ , p₀≟_)) (p , neq) =
      let p′ = unreplace p₀ p₀≟_ p , RemoveRespectEquiv.neq-equiv nothing (unreplace-isolated-equiv p₀ p₀≟_) p .fst neq
          p″ = just (the (G .Pos s ∖ p₀) (p , neq)) , nothing≢just
      in Remove≡ $
        remove-nothing p′ .fst
          ≡[ i ]⟨ remove-nothing (Remove≡ {x = p′} {y = p″} (replace-isolated-β-no p₀ p₀≟_ neq) i) .fst ⟩
        remove-nothing p″ .fst
          ≡⟨⟩
        p
          ∎

{-
cart-Iso : (F G : Container ℓ ℓ) → Iso (Cart (F ⊗Id) G) (Cart F (∂ G))
cart-Iso F G = go where
  _♭ : (g : Cart (F ⊗Id) G) → Cart F (∂ G)
  _♭ g = unit F ⋆ ∂[ g ]

  _♯ : (f : Cart F (∂ G)) → Cart (F ⊗Id) G
  _♯ f = [ f ]⊗Id ⋆ counit G

  rinv : section _♭ _♯
  rinv g =
    unit F ⋆ ∂[ [ g ]⊗Id ⋆ counit G ]
      ≡⟨ {! ⋆-assoc !} ⟩
    unit F ⋆ (∂[ [ g ]⊗Id ] ⋆ ∂[ counit G ])
      ≡⟨ {! !} ⟩
    (unit F ⋆ ∂[ [ g ]⊗Id ]) ⋆ ∂[ counit G ]
      ≡⟨ {! !} ⟩
    (g ⋆ unit (∂ G)) ⋆ ∂[ counit G ]
      ≡⟨ {! !} ⟩
    g ⋆ (unit (∂ G) ⋆ ∂[ counit G ])
      ≡⟨ cong (g ⋆_) (zag≡ G) ⟩
    g ⋆ id (∂ G)
      ≡⟨ {! !} ⟩
    g
      ∎

  opaque
    unfolding isIsolatedRespectEquiv

    linv : retract _♭ _♯
    linv g@([ gₛ ◁ gₚ ]) = Cart≡ refl $ funExt λ where
      (s , tt*) → equivExt λ q → {! !}

  go : Iso _ _
  go .Iso.fun = _♭
  go .Iso.inv = _♯
  go .Iso.rightInv = rinv
  go .Iso.leftInv = linv

cart-equiv : (F G : Container ℓ ℓ) → (Cart (F ⊗Id) G) ≃ (Cart F (∂ G))
cart-equiv F G .fst f = unit F ⋆ ∂[ f ]
cart-equiv F G .snd .equiv-proof g = goal where
  fiber-equiv : {! !} ≃ (fiber (λ f → unit F ⋆ ∂[ f ]) g)
  fiber-equiv =
    {! !}
      ≃⟨ {! !} ⟩
    Σ[ f ∈ Cart (F ⊗Id) G ] (unit F ⋆ ∂[ f ]) ≡ g
      ≃∎
  goal : isContr (fiber (λ f → unit F ⋆ ∂[ f ]) g)
  goal = {! !}

cart-equiv' : (F G : Container ℓ ℓ) → (Cart F (∂ G)) ≃ (Cart (F ⊗Id) G)
cart-equiv' F G .fst g = [ g ]⊗Id ⋆ counit G
cart-equiv' F G .snd = isoToIsEquiv (invIso (cart-Iso F G))

universal-arrow : (G : Container ℓ ℓ) → ∀ F → (g : Cart (F ⊗Id) G) → ∃![ g* ∈ Cart F (∂ G) ] [ g* ]⊗Id ⋆ counit G ≡ g
universal-arrow G F g = cart-equiv' F G .snd .equiv-proof g
-}
