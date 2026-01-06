{-# OPTIONS --safe #-}
module Derivative.Basics.Equiv where

open import Derivative.Prelude
open import Derivative.Basics.Sigma

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level
    A B C : Type ℓ

equivSquareP :
  {A B : I → I → Type ℓ}
  {e₀₀ : (A i0 i0) ≃ (B i0 i0)}
  {e₀₁ : (A i0 i1) ≃ (B i0 i1)}
  {e₀₋ : PathP (λ j → (A i0 j) ≃ (B i0 j)) e₀₀ e₀₁}
  {e₁₀ : (A i1 i0) ≃ (B i1 i0)}
  {e₁₁ : (A i1 i1) ≃ (B i1 i1)}
  {e₁₋ : PathP (λ j → (A i1 j) ≃ (B i1 j)) e₁₀ e₁₁}
  {e₋₀ : PathP (λ i → (A i i0) ≃ (B i i0)) e₀₀ e₁₀}
  {e₋₁ : PathP (λ i → (A i i1) ≃ (B i i1)) e₀₁ e₁₁}
  → SquareP (λ i j → A i j → B i j) (congP (λ _ → equivFun) e₀₋) (congP (λ _ → equivFun) e₁₋) (congP (λ _ → equivFun) e₋₀) (congP (λ _ → equivFun) e₋₁)
  → SquareP (λ i j → A i j ≃ B i j) e₀₋ e₁₋ e₋₀ e₋₁
equivSquareP = ΣSquarePProp isPropIsEquiv

equivPathPEquiv : ∀ {ℓ ℓ′} {A : I → Type ℓ} {B : I → Type ℓ′}
  → {e₀ : A i0 ≃ B i0} {e₁ : A i1 ≃ B i1}
  → PathP (λ i → A i → B i) (equivFun e₀) (equivFun e₁) ≃ PathP (λ i → A i ≃ B i) e₀ e₁
equivPathPEquiv {A} {B} {e₀} {e₁} = isoToEquiv iso module equivPathPEquiv where
  iso : Iso _ _
  iso .Iso.fun = equivPathP
  iso .Iso.inv = congP (λ i → equivFun)
  iso .Iso.rightInv _ = ΣSquarePProp isPropIsEquiv refl
  iso .Iso.leftInv _ = refl

invEquivPathP : ∀ {ℓ ℓ′} {A : I → Type ℓ} {B : I → Type ℓ′}
  → {e₀ : A i0 ≃ B i0} {e₁ : A i1 ≃ B i1}
  → PathP (λ i → B i → A i) (invEq e₀) (invEq e₁)
  → PathP (λ i → A i ≃ B i) e₀ e₁
invEquivPathP {A} {B} {e₀} {e₁} p = equivPathP p⁺ where
  p⁻ : PathP (λ i → B i ≃ A i) (invEquiv e₀) (invEquiv e₁)
  p⁻ = equivPathP p

  p⁺-ext : {a₀ : A i0} {a₁ : A i1}
    → PathP A a₀ a₁
    → PathP B (equivFun e₀ a₀) (equivFun e₁ a₁)
  p⁺-ext {a₀} {a₁} a₀≡a₁ i = invEq (p⁻ i) (a₀≡a₁ i)

  p⁺ : PathP (λ i → A i → B i) (equivFun e₀) (equivFun e₁)
  p⁺ = funExtNonDep p⁺-ext

preCompEquivFiberEquiv : (e : A ≃ B) (f : B → C) → ∀ c → fiber (equivFun e ⨟ f) c ≃ fiber f c
preCompEquivFiberEquiv {A} {B} {C} e f c =
  Σ[ a ∈ A ] f (equivFun e a) ≡ c
    ≃⟨ ⨟-fiber-equiv (equivFun e) f c ⟩
  Σ[ (b , _) ∈ fiber f c ] fiber (equivFun e) b
    ≃⟨ Σ-contractSnd (λ (b , _) → equivIsEquiv e .equiv-proof b) ⟩
  Σ[ b ∈ B ] f b ≡ c
    ≃∎

equivAdjointEquivExtCodomain : (e : A ≃ B) (f : C → A) (g : C → B)
  → (f ≡ invEq e ∘ g) ≃ (equivFun e ∘ f ≡ g)
equivAdjointEquivExtCodomain {C} e f g = invEquiv funExtEquiv ∙ₑ equivΠCod lemma ∙ₑ funExtEquiv where
  lemma : ∀ (c : C) → (f c ≡ invEq e (g c)) ≃ (equivFun e (f c) ≡ g c)
  lemma c = equivAdjointEquiv e

equivAdjointEquivExtDomain : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : Type ℓ'}
  → (e : A ≃ B) (f : B → C) (g : A → C)
  → (g ∘ invEq e ≡ f) ≃ (g ≡ f ∘ equivFun e)
equivAdjointEquivExtDomain {B} {C} =
  EquivJ
    (λ A e → (f : B → C) (g : A → C) → (g ∘ invEq e ≡ f) ≃ (g ≡ f ∘ equivFun e))
    (λ f g → idEquiv (g ≡ f))

lineEquiv : ∀ {A B : I → Type ℓ} (f : (i : I) → A i → B i)
  → (is-equiv₀ : isEquiv (f i0))
  → (is-equiv₁ : isEquiv (f i1))
  → ∀ φ → A φ ≃ B φ
lineEquiv f is-equiv₀ is-equiv₁ φ = λ where
  .fst → f φ
  .snd → isProp→PathP (λ i → isPropIsEquiv (f i)) is-equiv₀ is-equiv₁ φ

secEquiv : (e : A ≃ B) → ∀ (φ : I) → B ≃ B
secEquiv {B} e = lineEquiv (λ φ b → secEq e b φ) (equivIsEquiv (invEquiv e ∙ₑ e)) (idIsEquiv B)

retEquiv : (e : A ≃ B) → ∀ (φ : I) → A ≃ A
retEquiv {A} e = lineEquiv (λ φ a → retEq e a φ) (equivIsEquiv (e ∙ₑ invEquiv e)) (idIsEquiv A)

module _ {ℓ'} {A B : Type ℓ} where
  univalenceᴰ-Iso : (e : A ≃ B)
    → {P : A → Type ℓ'} {Q : B → Type ℓ'}
    → Iso (PathP (λ i → ua e i → Type ℓ') P Q) (Σ[ F ∈ mapOver (e .fst) P Q ] isEquivOver {P = P} {Q = Q} F)
  univalenceᴰ-Iso = EquivJ
    (λ A e → {P : A → Type ℓ'} {Q : B → Type ℓ'} → Iso (PathP (λ i → ua e i → Type ℓ') P Q) (Σ[ F ∈ mapOver (e .fst) P Q ] isEquivOver {P = P} {Q = Q} F))
    d
    where
      d : ∀ {P Q : B → Type ℓ'} → Iso (PathP (λ i → ua (idEquiv B) i → Type ℓ') P Q) (Σ[ F ∈ mapOver (idfun B) P Q ] isEquivOver {P = P} {Q = Q} F)
      d {P} {Q} =
        (PathP (λ i → ua (idEquiv B) i → Type ℓ') P Q)
          Iso⟨ substIso (λ p → PathP (λ i → p i → Type ℓ') P Q) uaIdEquiv ⟩
        (P ≡ Q)
          Iso⟨ invIso funExtIso ⟩
        ((b : B) → P b ≡ Q b)
          Iso⟨ codomainIsoDep (λ b → univalenceIso) ⟩
        ((b : B) → P b ≃ Q b)
          Iso⟨ Σ-Π-Iso ⟩
        Σ[ f ∈ ((b : B) → P b → Q b) ] ((b : B) → isEquiv (f b))
          ∎Iso

  univalenceᴰ : (e : A ≃ B)
    → {P : A → Type ℓ'} {Q : B → Type ℓ'}
    → (PathP (λ i → ua e i → Type ℓ') P Q) ≃ (Σ[ F ∈ mapOver (e .fst) P Q ] isEquivOver {P = P} {Q = Q} F)
  univalenceᴰ e = isoToEquiv $ univalenceᴰ-Iso e
