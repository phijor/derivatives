{-# OPTIONS --safe #-}
module Derivative.Properties where

open import Derivative.Prelude
open import Derivative.Basics.Decidable as Dec
open import Derivative.Basics.Maybe
open import Derivative.Basics.Sum as Sum using (_⊎_ ; inl ; inr)
open import Derivative.Basics.Unit
open import Derivative.Basics.W as W using (W)

open import Derivative.Isolated
open import Derivative.Remove

open import Derivative.Container
open import Derivative.Derivative

open import Cubical.Foundations.Equiv.Properties
import      Cubical.Foundations.Univalence as Univalence
import      Cubical.Foundations.Transport as Transport
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (uninhabEquiv)
open import  Cubical.HITs.SetTruncation as ST using (∥_∥₂)

private
  variable
    ℓ ℓS ℓP : Level

open Container
open Cart

∂-Const : (S : Type ℓ) → Equiv (∂ (Const S)) (Const 𝟘*)
∂-Const S .Equiv.shape = uninhabEquiv (λ ()) (λ ())
∂-Const S .Equiv.pos ()

∂-prop-trunc : (S : Type ℓ) {P : S → Type ℓ} → (∀ s → isProp (P s))
  → Equiv (∂ (S ◁ P)) (Σ S P ◁ const 𝟘*)
∂-prop-trunc S {P} is-prop-P =
  ∂ (S ◁ P)
    ⊸≃⟨⟩
  [ (s , p , _) ∈ Σ[ s ∈ S ] (P s) ° ]◁ (P s ∖ p)
    ⊸≃⟨ Equiv-fst $ Σ-cong-equiv-snd (λ s → isProp→IsolatedEquiv (is-prop-P s)) ⟩
  [ (s , p) ∈ Σ S P ]◁ (P s ∖ p)
    ⊸≃⟨ Equiv-snd (λ (s , p) → uninhabEquiv (λ ()) (isProp→isEmptyRemove (is-prop-P s) p)) ⟩
  [ (s , p) ∈ Σ S P ]◁ 𝟘*
    ⊸≃∎

∂-prop : (P : Type ℓ) → isProp P → Equiv (∂ (𝟙* {ℓ} ◁ const P)) (P ◁ const 𝟘*)
∂-prop {ℓ} P is-prop-P =
  ∂ (𝟙* {ℓ} ◁ const P)
    ⊸≃⟨ ∂-prop-trunc 𝟙* {P = const P} (const is-prop-P) ⟩
  ((𝟙* × P) ◁ const 𝟘*)
    ⊸≃⟨ Equiv-fst 𝟙*-unit-×-left-equiv ⟩
  (P ◁ const 𝟘*)
    ⊸≃∎

∂-Id : Equiv (∂ Id) (Const (𝟙* {ℓ}))
∂-Id = ∂-prop 𝟙* isProp-𝟙*

𝕂 : (A : Type ℓ) → Container ℓ ℓ
𝕂 A .Shape = A
𝕂 A .Pos = const 𝟘*

𝕪[_] : (A : Type ℓ) → Container ℓ ℓ
𝕪[ A ] .Shape = 𝟙*
𝕪[ A ] .Pos = const A

∂-𝕪° : (A : Type ℓ) → (a° : A °) → Equiv (∂ 𝕪[ A ]) ([ a ∈ A ° ]◁ (A ∖° a))
∂-𝕪° {ℓ} A a°@(a₀ , a₀≟_) =
  ∂ (𝟙* ◁ const A)
    ⊸≃⟨⟩
  ([ (_ , a) ∈ 𝟙* × (A °) ]◁ (A ∖° a))
    ⊸≃⟨ Equiv-fst 𝟙*-unit-×-left-equiv ⟩
  ([ a ∈ A ° ]◁ (A ∖° a))
    ⊸≃∎

∂-𝕪 : (A : Type ℓ) → Discrete A → Equiv (∂ 𝕪[ A ⊎ 𝟙* ]) (𝕂 (A ⊎ 𝟙*) ⊗ 𝕪[ A ])
∂-𝕪 {ℓ} A discrete-A = [ isoToEquiv shape-Iso ◁≃ invEquiv ∘ pos-equiv ] where
  shape-Iso : Iso _ _
  shape-Iso .Iso.fun (_ , x , _) = x , _
  shape-Iso .Iso.inv (just a , _) = _ , just° (a , discrete-A a)
  shape-Iso .Iso.inv (nothing , _) = _ , nothing°
  shape-Iso .Iso.rightInv (just a , _) = refl
  shape-Iso .Iso.rightInv (nothing , _) = refl
  shape-Iso .Iso.leftInv (_ , just a , _) = ≡-× refl (Isolated≡ $ refl′ $ just a)
  shape-Iso .Iso.leftInv (_ , nothing , _) = ≡-× refl (Isolated≡ $ refl′ nothing)

  pos-equiv : ((_ , x) : _ × (Maybe A °)) → ((Maybe A) ∖° x) ≃ (𝟘* ⊎ A)
  pos-equiv (_ , x) = e x ∙ₑ (Sum.⊎-empty-left λ ()) where
    e : (x : Maybe A °) → ((Maybe A) ∖° x) ≃ A
    e (nothing , _) = removeNothingEquiv
    e (just a , isolated-just-a) = removeJustEquiv a $ isIsolatedFromJust isolated-just-a

module _ (F G : Container ℓ ℓ) where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  sum-shape : (Σ[ x ∈ S ⊎ T ] Pos (F ⊕ G) x °) ≃ ((Σ[ s ∈ S ] P s °) ⊎ (Σ[ t ∈ T ] Q t °))
  sum-shape = Sum.Σ-⊎-fst-≃

  sum-rule : Equiv (∂ (F ⊕ G)) (∂ F ⊕ ∂ G)
  sum-rule .Equiv.shape = sum-shape
  sum-rule .Equiv.pos = uncurry (Sum.elim (λ s p → idEquiv (P s ∖ p .fst)) (λ t q → idEquiv (Q t ∖ q .fst)))

module _ (F G : Container ℓ ℓ) where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  prod-shape :
    (Σ[ (s , t) ∈ S × T ] (P s ⊎ Q t) °)
      ≃
    (((Σ[ s ∈ S ] P s °) × T) ⊎ (S × (Σ[ t ∈ T ] Q t °)))
  prod-shape =
    (Σ[ (s , t) ∈ S × T ] (P s ⊎ Q t) °)
      ≃⟨ Σ-cong-equiv-snd (λ _ → IsolatedSumEquiv) ⟩
    (Σ[ (s , t) ∈ S × T ] (P s °) ⊎ (Q t °))
      ≃⟨ Sum.Σ-⊎-snd-≃ ⟩
    ((Σ[ (s , _) ∈ S × T ] P s °) ⊎ (Σ[ (_ , t) ∈ S × T ] (Q t °)))
      ≃⟨ Sum.⊎-equiv shuffle-left shuffle-right ⟩
    (((Σ[ s ∈ S ] P s °) × T) ⊎ (S × (Σ[ t ∈ T ] Q t °)))
      ≃∎
      where
        shuffle-left : _ ≃ _
        shuffle-left = strictEquiv (λ ((s , t) , p) → ((s , p) , t)) (λ ((s , p) , t) → ((s , t) , p))

        shuffle-right : _ ≃ _
        shuffle-right = strictEquiv (λ ((s , t) , q) → (s , (t , q))) (λ (s , (t , q)) → ((s , t) , q))

  prod-rule : Equiv (∂ (F ⊗ G)) ((∂ F ⊗ G) ⊕ (F ⊗ ∂ G))
  prod-rule .Equiv.shape = prod-shape
  prod-rule .Equiv.pos = uncurry λ where
    (s , t) (inl p , _) → remove-left-equiv
    (s , t) (inr q , _) → remove-right-equiv

module _ {Ix : Type ℓ} (F : Ix → Container ℓ ℓ) where
  ∑ : Container ℓ ℓ
  ∑ .Shape = Σ[ ix ∈ Ix ] F ix .Shape
  ∑ .Pos (ix , s) = F ix .Pos s

module _ {Ix : Type ℓ} (F : Ix → Container ℓ ℓ) where
  sum'-rule : Equiv (∂ (∑ F)) (∑ (∂ ∘ F))
  sum'-rule .Equiv.shape = Σ-assoc-≃
  sum'-rule .Equiv.pos ((ix , s) , p , _) = idEquiv $ F ix .Pos s ∖ p

import Derivative.Basics.RusselsParadox as RP

no-weak-terminal : ¬ (Σ[ Y ∈ Container ℓ ℓ ] ∀ (X : Container ℓ ℓ) → Cart X Y)
no-weak-terminal {ℓ} (Y@(T ◁ Q) , inh-cart) = RP.noSmallUniverseOfTypes (T , Q , code , code-sec) where
  Q-fiber-equiv : (P : Type ℓ) → Cart (𝕪 P) (T ◁ Q) ≃ fiber Q P
  Q-fiber-equiv P =
    Cart (𝕪 P) (T ◁ Q)
      ≃⟨ Cart-Σ-equiv ⟩
    Σ[ t ∈ (𝟙* → T) ] ((x : 𝟙*) → Q (t x) ≃ P)
      ≃⟨ invEquiv Σ-Π-≃ ⟩
    (𝟙* → Σ[ t ∈ T ] Q t ≃ P)
      ≃⟨ Π𝟙*-equiv _ ⟩
    Σ[ t ∈ T ] Q t ≃ P
      ≃⟨ Σ-cong-equiv-snd (λ t → invEquiv Univalence.univalence) ⟩
    Σ[ t ∈ T ] Q t ≡ P
      ≃∎

  Q-inh-fiber : ∀ P → fiber Q P
  Q-inh-fiber P = equivFun (Q-fiber-equiv P) (inh-cart (𝕪 P))

  code : Type ℓ → T
  code = fst ∘ Q-inh-fiber

  code-sec : ∀ X → Q (code X) ≡ X
  code-sec = snd ∘ Q-inh-fiber

no-terminal : ¬ (Σ[ Y ∈ Container ℓ ℓ ] ∀ (X : Container ℓ ℓ) → isContr (Cart X Y))
no-terminal (Y , contr-cart) = no-weak-terminal (Y , fst ∘ contr-cart)

private
  isEmpty→isContrΠ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
    → (¬ A) → isContr (∀ a → B a)
  isEmpty→isContrΠ ¬A .fst = ex-falso ∘ ¬A
  isEmpty→isContrΠ ¬A .snd f = funExt $ ex-falso ∘ ¬A

no-internal-hom : ¬ (Σ[ _⇒_ ∈ ((F G : Container ℓ ℓ) → Container ℓ ℓ) ] ∀ F G H → Cart (F ⊗ G) H ≃ Cart F (G ⇒ H))
no-internal-hom {ℓ} (_⇒_ , adj) = no-terminal (_ , is-terminal-∅⇒∅) where
  ∅ : Container ℓ ℓ
  ∅ .Shape = 𝟘*
  ∅ .Pos ()

  is-contr-into-∅ : (X : Container ℓ ℓ) → isContr (Cart (X ⊗ ∅) ∅)
  is-contr-into-∅ X@(S ◁ P) = isOfHLevelRespectEquiv 0 (invEquiv equiv) isContr-𝟙* where
    equiv : (Cart (X ⊗ ∅) ∅) ≃ 𝟙
    equiv =
      Cart (X ⊗ ∅) ∅
        ≃⟨ Cart-Σ-equiv ⟩
      Σ[ f ∈ ((S × 𝟘*) → 𝟘*) ] ((s : S × Shape ∅) → Pos ∅ (f s) ≃ (P (s .fst) ⊎ Pos ∅ (s .snd)))
        ≃⟨ Σ-contractSnd (λ f → isEmpty→isContrΠ λ ()) ⟩
      ((S × 𝟘*) → 𝟘*)
        ≃⟨ isContr→≃𝟙* (isEmpty→isContrΠ λ ()) ⟩
      𝟙
        ≃∎

  is-terminal-∅⇒∅ : (X : Container ℓ ℓ) → isContr (Cart X (∅ ⇒ ∅))
  is-terminal-∅⇒∅ X = isOfHLevelRespectEquiv 0 (adj X ∅ ∅) $ is-contr-into-∅ X

no-weak-terminal-set : ¬ (Σ[ Y ∈ SetContainer ℓ ℓ ] ∀ (X : SetContainer ℓ ℓ) → SetCart X Y)
no-weak-terminal-set {ℓ} ((Y@(T ◁ Q) , is-set-T , is-set-Q) , inh-set-cart) = RP.noSmallUniverseOfSets (T* , Q* , code , code-sec) where
  T* : hSet ℓ
  T* = T , is-set-T

  Q* : T → hSet ℓ
  Q* t = Q t , is-set-Q t

  𝕪-set : hSet ℓ → SetContainer ℓ ℓ
  𝕪-set P .fst = 𝕪 ⟨ P ⟩
  𝕪-set P .snd .fst = isSet-𝟙*
  𝕪-set P .snd .snd _ = str P

  Q*-fiber-equiv : (P : hSet ℓ) → Cart (𝕪 ⟨ P ⟩) (T ◁ Q) ≃ fiber Q* P
  Q*-fiber-equiv P*@(P , _) =
    Cart (𝕪 P) (T ◁ Q)
      ≃⟨ Cart-Σ-equiv ⟩
    Σ[ t ∈ (𝟙* → T) ] ((x : 𝟙*) → Q (t x) ≃ P)
      ≃⟨ invEquiv Σ-Π-≃ ⟩
    (𝟙* → Σ[ t ∈ T ] Q t ≃ P)
      ≃⟨ Π𝟙*-equiv _ ⟩
    Σ[ t ∈ T ] Q t ≃ P
      ≃⟨ Σ-cong-equiv-snd (λ t → invEquiv Univalence.univalence) ⟩
    Σ[ t ∈ T ] Q t ≡ P
      ≃⟨ Σ-cong-equiv-snd (λ t → Σ≡PropEquiv λ _ → isPropIsSet) ⟩
    Σ[ t ∈ T ] Q* t ≡ P*
      ≃∎

  Q*-inh-fiber : ∀ P → fiber Q* P
  Q*-inh-fiber P = equivFun (Q*-fiber-equiv P) (inh-set-cart (𝕪-set P))

  code : hSet ℓ → T
  code = fst ∘ Q*-inh-fiber

  code-sec : ∀ X → Q* (code X) ≡ X
  code-sec = snd ∘ Q*-inh-fiber

private
  _⊗ₛ_ : SetContainer ℓ ℓ → SetContainer ℓ ℓ → SetContainer ℓ ℓ
  ((F , is-set-F) ⊗ₛ (G , is-set-G)) .fst = F ⊗ G
  ((F , is-set-F) ⊗ₛ (G , is-set-G)) .snd .fst = isSet× (is-set-F .fst) (is-set-G .fst)
  ((F , is-set-F) ⊗ₛ (G , is-set-G)) .snd .snd (s , t) = Sum.isSet⊎ (is-set-F .snd s) (is-set-G .snd t)

no-internal-hom-set : ¬ (Σ[ _⇒_ ∈ ((F G : SetContainer ℓ ℓ) → SetContainer ℓ ℓ) ] ∀ F G H → SetCart (F ⊗ₛ G) H → SetCart F (G ⇒ H))
no-internal-hom-set {ℓ} (_⇒_ , curry) = no-weak-terminal-set (∅ ⇒ ∅ , is-weak-terminal-∅⇒∅) where
  ∅ : SetContainer ℓ ℓ
  ∅ .fst .Shape = 𝟘*
  ∅ .fst .Pos ()
  ∅ .snd .fst ()
  ∅ .snd .snd ()

  is-weak-terminal-∅⇒∅ : (X : SetContainer ℓ ℓ) → SetCart X (∅ ⇒ ∅)
  is-weak-terminal-∅⇒∅ X = curry X ∅ ∅ λ where
    .Cart.shape ()
    .Cart.pos ()
