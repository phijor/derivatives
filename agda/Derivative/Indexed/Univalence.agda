{-# OPTIONS --safe #-}
module Derivative.Indexed.Univalence where

open import Derivative.Prelude
open import Derivative.Basics.Equiv using (univalenceᴰ ; symEquiv)
open import Derivative.Indexed.Container

open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence


private
  variable
    ℓ : Level
    Ix : Type ℓ

module _ (F G : Container ℓ Ix) where
  open Container F renaming (Shape to S ; Pos to P)
  open Container G renaming (Shape to T ; Pos to Q)

  Coverᴰ : (f : S ≃ T) → Type _
  Coverᴰ f = ∀ ix → Σ[ e ∈ mapOver (equivFun f) (P ix) (Q ix) ] isEquivOver {Q = Q ix} e

  Cover : Type _
  Cover = Σ[ f ∈ S ≃ T ] Coverᴰ f

  Equiv≃Cover : (Equiv F G) ≃ Cover
  Equiv≃Cover =
    Equiv F G
      ≃⟨ Equiv-Σ-equiv F G ⟩
    Σ[ f ∈ S ≃ T ] (∀ ix s → Q ix (equivFun f s) ≃ P ix s)
      ≃⟨ Σ-cong-equiv-snd snd-equiv ⟩
    Cover
      ≃∎ where
    snd-equiv : (f : S ≃ T) → (∀ ix s → Q ix (equivFun f s) ≃ P ix s) ≃ Coverᴰ f
    snd-equiv f =
      (∀ ix s → Q ix (equivFun f s) ≃ P ix s)
        ≃⟨ equivΠCod (λ ix → equivΠCod λ s → invEquivEquiv) ⟩
      (∀ ix s → P ix s ≃ Q ix (equivFun f s))
        ≃⟨ equivΠCod (λ ix → Σ-Π-≃) ⟩
      (∀ ix → Σ[ e ∈ (∀ s → P ix s → Q ix (equivFun f s)) ] (∀ s → isEquiv (e s)))
        ≃∎

  Cover≃Path : Cover ≃ (F ≡ G)
  Cover≃Path =
    Cover
      ≃⟨ Σ-cong-equiv-snd (λ e → equivΠCod λ ix → invEquiv (univalenceᴰ e)) ⟩
    Σ[ e ∈ S ≃ T ] (∀ ix → PathP (λ i → ua e i → Type ℓ) (P ix) (Q ix))
      ≃⟨ Σ-cong-equiv-fst (invEquiv univalence) ⟩
    Σ[ p ∈ S ≡ T ] (∀ ix → PathP (λ i → p i → Type ℓ) (P ix) (Q ix))
      ≃⟨ Σ-cong-equiv-snd (λ p → funExtEquiv) ⟩
    Σ[ p ∈ S ≡ T ] (PathP (λ i → Ix → p i → Type ℓ) P Q)
      ≃⟨ ΣPathP≃PathPΣ ⟩
    (S , P) ≡ (T , Q)
      ≃⟨ invEquiv (congEquiv Container-Σ-equiv) ⟩
    (F ≡ G)
      ≃∎

  Equiv≃Path : (Equiv F G) ≃ (F ≡ G)
  Equiv≃Path = Equiv≃Cover ∙ₑ Cover≃Path

ContainerEquivContr : (G : Container ℓ Ix) → ∃![ F ∈ Container _ _ ] Equiv F G
ContainerEquivContr G = isOfHLevelRespectEquiv 0 (Σ-cong-equiv-snd λ F → symEquiv ∙ₑ invEquiv (Equiv≃Path F G)) (isContrSingl G)

contrContainerSinglEquiv : {F G : Container ℓ Ix}
  → (e : Equiv F G)
  → (G , idₑ G) ≡ (F , e)
contrContainerSinglEquiv {F} {G} e = isContr→isProp (ContainerEquivContr G) (G , idₑ G) (F , e)

opaque
  ContainerEquivJ : ∀ {ℓ'} {F G : Container ℓ Ix}
    → (P : (F : Container ℓ Ix) → Equiv F G → Type ℓ')
    → (r : P G (idₑ G))
    → (e : Equiv F G) → P F e
  ContainerEquivJ P r e = subst (λ (F , e) → P F e) (contrContainerSinglEquiv e) r

isEquivContainerEquivPreComp : {F G : Container ℓ Ix}
  → (e : F ⧟ G)
  → (H : Container ℓ Ix)
  → isEquiv (λ (g : G ⊸ H) → Equiv.as-⊸ e ⋆ g)
isEquivContainerEquivPreComp {ℓ} {Ix} {G} = ContainerEquivJ
  (λ F e → ∀ H → isEquiv (λ (g : G ⊸ H) → Equiv.as-⊸ e ⋆ g))
  is-equiv-at-id
  where
    is-equiv-at-id : (H : Container ℓ Ix) → isEquiv (λ (g : G ⊸ H) → Equiv.as-⊸ (idₑ G) ⋆ g)
    is-equiv-at-id H = isoToIsEquiv iso where
      iso : Iso (G ⊸ H) (G ⊸ H)
      iso .Iso.fun = Equiv.as-⊸ (idₑ G) ⋆_
      iso .Iso.inv = idfun _
      iso .Iso.rightInv g = ⋆-id-left g
      iso .Iso.leftInv g = ⋆-id-left g

containerEquivPreCompEquiv : {F G : Container ℓ Ix}
  → (e : F ⧟ G)
  → (H : Container ℓ Ix)
  → (G ⊸ H) ≃ (F ⊸ H)
containerEquivPreCompEquiv e H .fst = Equiv.as-⊸ e ⋆_
containerEquivPreCompEquiv e H .snd = isEquivContainerEquivPreComp e H
