module Derivative.Embedding where

open import Derivative.Prelude

open import Cubical.Functions.Embedding

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
isEmbeddingPrecompEquiv→isEmbedding = {! !}

isEmbeddingPostecompEquiv→isEmbedding : (f : A → B) (e : B ≃ C)
  → isEmbedding (f ⨟ equivFun e)
  → isEmbedding f
isEmbeddingPostecompEquiv→isEmbedding = {! !}

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
