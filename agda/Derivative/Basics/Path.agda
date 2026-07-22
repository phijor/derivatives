{-# OPTIONS --safe #-}
module Derivative.Basics.Path where

open import Derivative.Prelude

import      Cubical.Core.Primitives as Primitives
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties

private
  variable
    ℓ : Level
    A B : Type ℓ

hcompᴵ : (φ : I) (u : ∀ i → Partial (φ ∨ ~ i) A) → A
hcompᴵ {A} φ u = Primitives.hcomp {φ = φ} sys base module hcomp where
  base : A
  base = u i0 1=1
  {-# INLINE base #-}

  sys : I → Partial φ A
  sys i (φ = i1) = u i 1=1

compᴵ : (A : I → Type ℓ) (φ : I) (u : ∀ i → Partial (φ ∨ ~ i) (A i)) → A i1
compᴵ A φ u = Primitives.comp A {φ = φ} sys base module comp where
  base : A i0
  base = u i0 1=1
  {-# INLINE base #-}

  sys : (i : I) → Partial φ (A i)
  sys i (φ = i1) = u i 1=1

∂ᴵ : I → I
∂ᴵ i = i ∨ ~ i

Jᴰ : ∀ {ℓ ℓ'} {A : I → Type ℓ}
  → (x : A i0)
  → (P : ∀ {i : I} → (y : A i) → PathP (λ j → A (i ∧ j)) x y → Type ℓ')
  → (d : P x refl)
  → {y : A i1} (p : PathP A x y) → P y p
Jᴰ _ P d p = transport (λ i → P (p i) λ j → p (i ∧ j)) d

compSquare→PathP : (B : A → Type ℓ)
  → {x y z w : A}
  → {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} {s : x ≡ w}
  → (filler : Square (sym p) r q s)
  → {xᴰ : B x} {yᴰ : B y} {zᴰ : B z} {wᴰ : B w}
  → (pᴰ : PathP (λ i → B (p i)) xᴰ yᴰ)
  → (qᴰ : PathP (λ i → B (q i)) yᴰ zᴰ)
  → (rᴰ : PathP (λ i → B (r i)) zᴰ wᴰ)
  → PathP (λ i → B (s i)) xᴰ wᴰ
compSquare→PathP B filler pᴰ qᴰ rᴰ i =
  compᴵ (λ j → B (filler i j)) (∂ᴵ i)
  λ where
    j (i = i0) → pᴰ (~ j)
    j (i = i1) → rᴰ j
    j (j = i0) → qᴰ i

doubleCompPathP : (B : A → Type ℓ)
  → {x y z w : A}
  → {p : x ≡ y} {q : y ≡ z} {r : z ≡ w}
  → {xᴰ : B x} {yᴰ : B y} {zᴰ : B z} {wᴰ : B w}
  → (pᴰ : PathP (λ i → B (p i)) xᴰ yᴰ)
  → (qᴰ : PathP (λ i → B (q i)) yᴰ zᴰ)
  → (rᴰ : PathP (λ i → B (r i)) zᴰ wᴰ)
  → PathP (λ i → B ((p ∙∙ q ∙∙ r) i)) xᴰ wᴰ
doubleCompPathP B {p} {q} {r} = compSquare→PathP B λ i j → doubleCompPath-filler p q r j i

neqCongEquiv : {a b : A} {x y : B}
  → (a ≡ b) ≃ (x ≡ y)
  → (a ≢ b) ≃ (x ≢ y)
neqCongEquiv e = preCompEquiv (invEquiv e)

cong-compPath : {x y z : A}
  → (f : A → B)
  → (p : x ≡ y) (q : y ≡ z)
  → cong f (p ∙ q) ≡ (cong f p) ∙ (cong f q)
cong-compPath {x} {y} {z} f p q = cong fst $ compPath-unique refl (cong f p) (cong f q) filler-left filler-right where
  filler-left : Σ[ r ∈ f x ≡ f z ] PathP (λ i → f x ≡ f (q i)) (cong f p) r
  filler-left .fst = cong f (p ∙ q)
  filler-left .snd i j = f (compPath-filler p q i j)

  filler-right : Σ[ r ∈ f x ≡ f z ] PathP (λ i → f x ≡ f (q i)) (cong f p) r
  filler-right .fst = (cong f p) ∙ (cong f q)
  filler-right .snd = compPath-filler (cong f p) (cong f q)
