{-# OPTIONS --safe #-}
module Derivative.Basics.Embedding where

open import Derivative.Prelude
open import Derivative.Basics.Equiv
open import Derivative.Basics.Function
open import Derivative.Basics.Sigma

open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding public

private
  variable
    ℓ : Level
    A B C : Type ℓ

isEmbeddingComp : (f : A → B) (g : B → C)
  → isEmbedding f
  → isEmbedding g
  → isEmbedding (f ⨟ g)
isEmbeddingComp f g emb-f emb-g = isEmbedding-∘ {f = g} {h = f} emb-g emb-f

isEmbeddingPrecompEquiv→isEmbedding : (e : A ≃ B) (f : B → C)
  → isEmbedding (equivFun e ⨟ f)
  → isEmbedding f
isEmbeddingPrecompEquiv→isEmbedding e f emb-ef = hasPropFibers→isEmbedding prop-fibers where
  prop-fibers : ∀ c → isProp (fiber f c)
  prop-fibers c = isOfHLevelRespectEquiv 1 (preCompEquivFiberEquiv e f c)
    $ isEmbedding→hasPropFibers emb-ef c

postCompEmbeddingFiberEquiv : (f : A → B) (e : B → C) → isEmbedding e
  → ∀ b → fiber (f ⨟ e) (e b) ≃ fiber f b
postCompEmbeddingFiberEquiv f e emb-e b = Σ-cong-equiv-snd λ a → invEquiv $ cong e , emb-e (f a) b

isEmbeddingPostCompEmbedding→isEmbedding : (f : A → B) (e : B → C)
  → isEmbedding e
  → isEmbedding (f ⨟ e)
  → isEmbedding f
isEmbeddingPostCompEmbedding→isEmbedding f e emb-e emb-fe = hasPropFibers→isEmbedding prop-fibers where
  prop-fibers : ∀ b → isProp (fiber f b)
  prop-fibers b = isOfHLevelRespectEquiv 1 (postCompEmbeddingFiberEquiv f e emb-e b)
    $ isEmbedding→hasPropFibers emb-fe (e b)

isEmbeddingPostCompEquiv→isEmbedding : (f : A → B) (e : B ≃ C)
  → isEmbedding (f ⨟ equivFun e)
  → isEmbedding f
isEmbeddingPostCompEquiv→isEmbedding f e = isEmbeddingPostCompEmbedding→isEmbedding
  f
  (equivFun e)
  (isEquiv→isEmbedding (equivIsEquiv e))

isEmbeddingPostComp : (f : A → B)
  → isEmbedding f
  → isEmbedding (λ (φ : C → A) → f ∘ φ)
isEmbeddingPostComp {A} {B} {C} f emb-f = hasPropFibers→isEmbedding prop-fibers where
  prop-fibers : ∀ ψ → isProp (fiber (f ∘_) ψ)
  prop-fibers ψ = isOfHLevelRespectEquiv 1 (postCompFiberEquiv f ψ)
    $ isPropΠ λ c → isEmbedding→hasPropFibers emb-f (ψ c)

isEmbedding-Σ-map-fst : {B : C → Type ℓ} (f : A → C) → isEmbedding f → isEmbedding (Σ-map-fst {B′ = B} f)
isEmbedding-Σ-map-fst f emb-f = hasPropFibers→isEmbedding λ where
  y → isOfHLevelRetractFromIso 1 (Σ-map-fst-fiber-iso f) (isEmbedding→hasPropFibers emb-f (y .fst))

module _ {ℓB ℓB′} {A : Type ℓ} {B : A → Type ℓB} {B′ : A → Type ℓB′} where
  isEmbedding-Σ-map-snd : {f : ∀ a → B a → B′ a} → (∀ a → isEmbedding (f a)) → isEmbedding (Σ-map-snd f)
  isEmbedding-Σ-map-snd {f} emb-f = hasPropFibers→isEmbedding λ where
    y → isOfHLevelRetractFromIso 1 Σ-map-snd-fiber-iso $ isEmbedding→hasPropFibers (emb-f (y .fst)) (y .snd)

isEmbedding-Σ-map : ∀ {ℓB ℓB′} {A′ : Type ℓ} {B : A → Type ℓB} {B′ : A′ → Type ℓB′}
  → {f : A → A′}
  → {g : ∀ a → B a → B′ (f a)}
  → isEmbedding f
  → (∀ a → isEmbedding (g a))
  → isEmbedding (Σ-map {B′ = B′} f g)
isEmbedding-Σ-map {f} {g} emb-f emb-g = isEmbeddingComp (Σ-map-snd g) (Σ-map-fst f) (isEmbedding-Σ-map-snd emb-g) (isEmbedding-Σ-map-fst f emb-f)

isPropMap→isEmbedding : (f : A → B) → isProp A → isProp B → isEmbedding f
isPropMap→isEmbedding f is-prop-A is-prop-B = hasPropFibers→isEmbedding λ b → isPropΣ is-prop-A λ a → isOfHLevelPath 1 is-prop-B (f a) b

isPropSnd→isEmbedding-Σ-map : ∀ {ℓB ℓB′} {A′ : Type ℓ} {B : A → Type ℓB} {B′ : A′ → Type ℓB′}
  → {f : A → A′}
  → {g : ∀ a → B a → B′ (f a)}
  → isEmbedding f
  → (∀ a → isProp (B a))
  → (∀ a → isProp (B′ (f a)))
  → isEmbedding (Σ-map {B′ = B′} f g)
isPropSnd→isEmbedding-Σ-map {g} emb-f is-prop-B is-prop-B′ = isEmbedding-Σ-map emb-f λ a → isPropMap→isEmbedding (g a) (is-prop-B _) (is-prop-B′ _)
