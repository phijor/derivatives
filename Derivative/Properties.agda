module Derivative.Properties where

open import Derivative.Prelude
open import Derivative.Container
open import Derivative.Derivative

open import Derivative.Decidable as Dec
open import Derivative.Isolated
open import Derivative.Maybe
open import Derivative.Remove
open import Derivative.Sum as Sum using (_⊎_ ; inl ; inr)

open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Empty as Empty using (⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

private
  variable
    ℓ ℓS ℓP : Level

  𝟘 : (ℓ : Level) → Type ℓ
  𝟘 _ = ⊥*

  𝟙 : (ℓ : Level) → Type ℓ
  𝟙 _ = Unit*

open Container
open Cart

∂-Const : (S : Type ℓ) → Equiv (∂ (Const S)) (Const (𝟘 _))
∂-Const S .Equiv.shape = Empty.uninhabEquiv (λ ()) lower
∂-Const S .Equiv.pos ()

∂-prop-trunc : (S : Type ℓ) {P : S → Type ℓ} → (∀ s → isProp (P s))
  → Equiv (∂ (S ◁ P)) (Σ S P ◁ const (𝟘 _))
∂-prop-trunc S {P} is-prop-P =
  ∂ (S ◁ P)
    ⊸≃⟨⟩
  [ (s , p , _) ∈ Σ[ s ∈ S ] (P s) ° ]◁ (P s ∖ p)
    ⊸≃⟨ Equiv-fst $ Σ-cong-equiv-snd (λ s → isProp→IsolatedEquiv (is-prop-P s)) ⟩
  [ (s , p) ∈ Σ S P ]◁ (P s ∖ p)
    ⊸≃⟨ Equiv-snd (λ (s , p) → Empty.uninhabEquiv (λ ()) (isProp→isEmptyRemove (is-prop-P s) p)) ⟩
  [ (s , p) ∈ Σ S P ]◁ (𝟘 _)
    ⊸≃∎

∂-prop : (P : Type ℓ) → isProp P → Equiv (∂ (𝟙 ℓ ◁ const P)) (P ◁ const (𝟘 _))
∂-prop {ℓ} P is-prop-P =
  ∂ (𝟙 ℓ ◁ const P)
    ⊸≃⟨ ∂-prop-trunc (𝟙 _) {P = const P} (const is-prop-P) ⟩
  ((𝟙 ℓ × P) ◁ const (𝟘 _))
    ⊸≃⟨ Equiv-fst (isoToEquiv lUnit*×Iso) ⟩
  (P ◁ const (𝟘 _))
    ⊸≃∎

∂-Id : Equiv (∂ Id) (Const (𝟙 ℓ))
∂-Id = ∂-prop (𝟙 _) isPropUnit*

𝕂 : (A : Type ℓ) → Container ℓ ℓ
𝕂 A .Shape = A
𝕂 A .Pos = const (𝟘 _)

𝕪[_] : (A : Type ℓ) → Container ℓ ℓ
𝕪[ A ] .Shape = 𝟙 _
𝕪[ A ] .Pos = const A

∂-𝕪° : (A : Type ℓ) → (a° : A °) → Equiv (∂ 𝕪[ A ]) ([ a ∈ A ° ]◁ (A - a))
∂-𝕪° {ℓ} A a°@(a₀ , a₀≟_) =
  ∂ (𝟙 _ ◁ const A)
    ⊸≃⟨⟩
  ([ (_ , a) ∈ 𝟙 ℓ × (A °) ]◁ (A - a))
    ⊸≃⟨ Equiv-fst (isoToEquiv lUnit*×Iso) ⟩
  ([ a ∈ A ° ]◁ (A - a))
    ⊸≃∎

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
    (s , t) (inl p , iso-p) → remove-left-equiv (isIsolatedFromInl iso-p)
    (s , t) (inr q , iso-q) → remove-right-equiv (isIsolatedFromInr iso-q)

module _ {Ix : Type ℓ} (F : Ix → Container ℓ ℓ) where
  ∑ : Container ℓ ℓ
  ∑ .Shape = Σ[ ix ∈ Ix ] F ix .Shape
  ∑ .Pos (ix , s) = F ix .Pos s

module _ {Ix : Type ℓ} (F : Ix → Container ℓ ℓ) where
  sum'-rule : Equiv (∂ (∑ F)) (∑ (∂ ∘ F))
  sum'-rule .Equiv.shape = Σ-assoc-≃
  sum'-rule .Equiv.pos ((ix , s) , p , _) = idEquiv $ F ix .Pos s ∖ p
