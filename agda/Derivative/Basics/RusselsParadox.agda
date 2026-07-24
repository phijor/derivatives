{-# OPTIONS --safe #-}
module Derivative.Basics.RusselsParadox where

open import Derivative.Prelude

open import Derivative.Basics.Decidable using (isProp¬)
open import Derivative.Basics.Sigma
open import Derivative.Basics.Unit
open import Derivative.Basics.W as W using (W)

open import Cubical.Foundations.Equiv.Properties using (hasSection)
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma

private
  _-Type : ∀ {ℓ} → (P : Type ℓ → Type ℓ) → Type (ℓ-suc ℓ)
  P -Type = Σ (Type _) P

module Subuniverse
  {ℓ}
  (P : Type ℓ → Type ℓ)
  (Σᴾ : {A : Type ℓ} {B : A → Type ℓ} → P A → (∀ a → isProp (B a)) → P (Σ A B))
  (Wᴾ : {A : Type ℓ} {B : A → Type ℓ} → P A → P (W A B))
  (U : P -Type)
  (El : ⟨ U ⟩ → P -Type)
  where

  V : Type ℓ
  V = W ⟨ U ⟩ (⟨_⟩ ∘ El)

  V-sup : (u : ⟨ U ⟩) → (⟨ El u ⟩ → V) → V
  V-sup = W.sup

  _∈_ : V → V → Type ℓ
  x ∈ W.sup _ el = fiber el x

  _∉_ : V → V → Type ℓ
  x ∉ X = ¬ (x ∈ X)

  not-in-self : P -Type
  not-in-self .fst = Σ[ x ∈ V ] x ∉ x
  not-in-self .snd = Σᴾ (Wᴾ (str U)) λ _ → isProp¬ _

  not-in-self-el : ⟨ not-in-self ⟩ → V
  not-in-self-el = fst

  noSmallSubuniverse : ¬ hasSection El
  noSmallSubuniverse (code , code-sec) = paradox where
    cast : (A : P -Type) → ⟨ El (code A) ⟩ → ⟨ A ⟩
    cast A = transport $ cong ⟨_⟩ $ (code-sec A)

    sup : (A : P -Type) → (⟨ A ⟩ → V) → V
    sup A el = V-sup (code A) (el ∘ cast A)

    R : V
    R = sup (not-in-self) not-in-self-el

    ∈-sup-equiv-inh-fiber : (A : P -Type) (el : ⟨ A ⟩ → V)
      → (x : V)
      → (x ∈ sup A el) ≃ fiber el x
    ∈-sup-equiv-inh-fiber A _ _ = Σ-cong-equiv-fst equiv-fst where
      equiv-fst : ⟨ El (code A) ⟩ ≃ ⟨ A ⟩
      equiv-fst = pathToEquiv (cong ⟨_⟩ $ code-sec A)

    in-R-iff-not-in-self : (X : V) → (X ∈ R) ≃ (X ∉ X)
    in-R-iff-not-in-self X =
      (Σ[ h ∈ ⟨ El (code not-in-self) ⟩ ] not-in-self-el (cast not-in-self h) ≡ X)
        ≃⟨ ∈-sup-equiv-inh-fiber not-in-self not-in-self-el X ⟩
      (Σ[ (x , _) ∈ ⟨ not-in-self ⟩ ] x ≡ X)
        ≃⟨ strictEquiv (λ ((u , h) , p) → (u , sym p) , h) (λ ((u , p) , h) → (u , h) , sym p) ⟩
      (Σ[ (u , _) ∈ singl X ] u ∉ u)
        ≃⟨ (Σ-contractFst (isContrSingl X)) ⟩
      (X ∉ X)
        ≃∎
      
    R∈R≃R∉R : (R ∈ R) ≃ (R ∉ R)
    R∈R≃R∉R = in-R-iff-not-in-self R

    R∉R : R ∉ R
    R∉R R∈R = equivFun R∈R≃R∉R R∈R R∈R

    R∈R : R ∈ R
    R∈R = invEq R∈R≃R∉R R∉R

    paradox : ⊥
    paradox = R∉R R∈R

noSmallUniverseOfTypes : ∀ {ℓ} → ¬ (Σ[ U ∈ Type ℓ ] Σ[ El ∈ (U → Type ℓ) ] hasSection El)
noSmallUniverseOfTypes {ℓ} (U , El , sec) = Subuniverse.noSmallSubuniverse
  isType is-type-Σ (λ {B = B} → is-type-W {B = B})
  (U , is-type-U) El* has-section-El*
  where
    isType : Type ℓ → Type ℓ
    isType _ = 𝟙*

    𝓤 : Type _
    𝓤 = isType -Type

    El* : U → 𝓤
    El* u .fst = El u
    El* u .snd = •

    has-section-El* : hasSection El*
    has-section-El* .fst = sec .fst ∘ fst
    has-section-El* .snd (A , •) = cong (_, •) (sec .snd A)

    is-type-U : isType U
    is-type-U = •

    is-type-Σ : ∀ {A : Type ℓ} {P : A → Type ℓ} → isType A → (∀ a → isProp (P a)) → isType (Σ A P)
    is-type-Σ _ _ = •

    is-type-W : ∀ {A : Type ℓ} {B : A → Type ℓ} → isType A → isType (W A B)
    is-type-W _ = •

noSmallUniverseOf_-Types : ∀ {ℓ} (n : HLevel) → ¬ (Σ[ U ∈ TypeOfHLevel ℓ (suc n) ] Σ[ El ∈ (⟨ U ⟩ → TypeOfHLevel ℓ (suc n)) ] hasSection El)
noSmallUniverseOf_-Types {ℓ} n (U , El , sec) = Subuniverse.noSmallSubuniverse
  (isOfHLevel (suc n)) (isOfHLevelSucΣSndProp n) (W.isOfHLevelSucW n)
  U El sec

noSmallUniverseOfSets : ∀ {ℓ} → ¬ (Σ[ U ∈ hSet ℓ ] Σ[ El ∈ (⟨ U ⟩ → hSet ℓ) ] hasSection El)
noSmallUniverseOfSets = noSmallUniverseOf 1 -Types
