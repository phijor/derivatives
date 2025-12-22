{-# OPTIONS --safe #-}

open import Derivative.Prelude
open import Derivative.Basics.Embedding
open import Derivative.Basics.Sigma
open import Derivative.Basics.Sum as Sum
open import Derivative.Basics.W
open import Derivative.Isolated.Base
open import Derivative.Isolated.Sum
open import Derivative.Remove

module Derivative.Isolated.W {ℓS ℓP ℓQ} {S : Type ℓS} {P : S → Type ℓP} {Q : S → Type ℓQ} where
private
  variable
    s : S
    f : P s → W S P

opaque
  isIsolatedTop : ∀ {q : Q s} → isIsolated q → isIsolated {A = Wᴰ S P Q (sup s f)} (top q)
  isIsolatedTop {s} {f} {q} = isIsolatedPreserveEquiv' (Wᴰ-out-equiv _ _ _ s f) (top q) ∘ isIsolatedInl

top° : Q s ° → Wᴰ S P Q (sup s f) °
top° = Σ-map top λ q → isIsolatedTop

isIsolatedFromTop : ∀ {q : Q s} → isIsolated {A = Wᴰ S P Q (sup s f)} (top q) → isIsolated q
isIsolatedFromTop {s} {f} {q} isolated-top = isIsolatedFromInl isolated-inl where
  isolated-inl : isIsolated {A = Q s ⊎ (Σ[ p ∈ P s ] (Wᴰ S P Q (f p)))} (inl q)
  isolated-inl = isIsolatedPreserveEquiv (Wᴰ-out-equiv _ _ _ s f) (top q) isolated-top

opaque
  isIsolatedBelow : ∀ {p : P s} {wᴰ : Wᴰ S P Q (f p)}
    → isIsolated {A = Σ[ p ∈ P s ] Wᴰ S P Q (f p)} (p , wᴰ)
    → isIsolated {A = Wᴰ S P Q (sup s f)} (below p wᴰ)
  isIsolatedBelow {s} {f} {p} {wᴰ} = isIsolatedPreserveEquiv' (Wᴰ-out-equiv _ _ _ s f) (below p wᴰ) ∘ isIsolatedInr

below° : (Σ[ p ∈ P s ] Wᴰ S P Q (f p)) ° → Wᴰ S P Q (sup s f) °
below° = Σ-map (uncurry below) λ _ → isIsolatedBelow

isIsolatedFromBelow : ∀ {p : P s} {wᴰ : Wᴰ S P Q (f p)}
  → isIsolated {A = Wᴰ S P Q (sup s f)} (below p wᴰ)
  → isIsolated {A = Σ[ p ∈ P s ] Wᴰ S P Q (f p)} (p , wᴰ)
isIsolatedFromBelow {s} {f} {p} {wᴰ} isolated-below = isIsolatedFromInr isolated-inr where
  isolated-inr : isIsolated {A = Q s ⊎ (Σ[ p ∈ P s ] (Wᴰ S P Q (f p)))} (inr (p , wᴰ))
  isolated-inr = isIsolatedPreserveEquiv (Wᴰ-out-equiv _ _ _ s f) (below p wᴰ) isolated-below

opaque
  isEmbeddingTop : ∀ {s f} → isEmbedding {B = Wᴰ S P Q (sup s f)} top
  isEmbeddingTop {s} {f} = isEmbeddingPostCompEquiv→isEmbedding top (Wᴰ-out-equiv _ _ _ s f) Sum.isEmbedding-inl

  isEmbeddingTop° : ∀ {s} {f} → isEmbedding {B = Wᴰ S P Q (sup s f) °} top°
  isEmbeddingTop° {s} {f} = isPropSnd→isEmbedding-Σ-map isEmbeddingTop isPropIsIsolated (isPropIsIsolated ∘ top)

  isEmbeddingBelow : ∀ {s f} → isEmbedding {A = Σ[ p ∈ P s ] Wᴰ S P Q (f p)} {B = Wᴰ S P Q (sup s f)} (uncurry below)
  isEmbeddingBelow {s} {f} = isEmbeddingPostCompEquiv→isEmbedding (uncurry below) (Wᴰ-out-equiv _ _ _ s f) Sum.isEmbedding-inr

  isEmbeddingBelow° : ∀ {s f} → isEmbedding {A = (Σ[ p ∈ P s ] Wᴰ S P Q (f p)) °} {B = Wᴰ S P Q (sup s f) °} below°
  isEmbeddingBelow° {s} {f} = isPropSnd→isEmbedding-Σ-map isEmbeddingBelow isPropIsIsolated (isPropIsIsolated ∘ uncurry below)

