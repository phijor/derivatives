module Derivative.Isolated where

open import Derivative.Prelude
open import Derivative.Decidable
  as Dec
  using
    ( locallyDiscrete→locallyIsPropPath
    ; Dec ; yes ; no
    ; Discrete
    ; _≢_
    ; ¬_
    )
open import Derivative.Remove


open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Properties using (EquivPresDec)
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit as Unit using (Unit*)

private
  variable
    ℓ : Level
    A B : Type ℓ

isIsolated : (a : A) → Type _
isIsolated a = ∀ b → Dec (a ≡ b)

-- There is at most one path to an isolated point:
isIsolated→isPropPath : (a : A) → isIsolated a → ∀ a′ → isProp (a ≡ a′)
isIsolated→isPropPath = locallyDiscrete→locallyIsPropPath

-- For an isolated point, decidability of equality is a proposition:
isIsolated→isPropDecPath : (a : A) → isIsolated a → ∀ a′ → isProp (Dec (a ≡ a′))
isIsolated→isPropDecPath a isolated a′ = Dec.isPropDec (isIsolated→isPropPath a isolated a′)

-- Being isolated is a proposition:
isPropIsIsolated : (a : A) → isProp (isIsolated a)
isPropIsIsolated a = isPropFromPointed→isProp go where
  go : isIsolated a → isProp (isIsolated a)
  go isolated = isPropΠ $ isIsolated→isPropDecPath a isolated

Isolated : (A : Type ℓ) → Type ℓ
Isolated A = Σ[ a ∈ A ] isIsolated a

_° : (A : Type ℓ) → Type ℓ
A ° = Isolated A

module _ {ℓB : Level} {B : A → Type ℓB}
  ((a₀ , a₀≟_) : A °)
  (eq* : ∀ a → a₀ ≡ a → B a)
  (neq* : (a : A ∖ a₀) → B (a .fst))
  where
  elimIsolated : ∀ a → B a
  elimIsolated a = Dec.elim (eq* a) (λ neq → neq* (a , neq)) (a₀≟ a)

  elimIsolated-β-yes : ∀ a → (p : a₀ ≡ a) → elimIsolated a ≡ eq* a p
  elimIsolated-β-yes a p i = Dec.elim (eq* a) (λ neq → neq* (a , neq)) (isIsolated→isPropDecPath a₀ a₀≟_ a (a₀≟ a) (yes p) i)

  elimIsolated-β-refl : elimIsolated a₀ ≡ eq* a₀ refl
  elimIsolated-β-refl = elimIsolated-β-yes a₀ refl

  elimIsolated-β-no : ∀ a → (¬p : a₀ ≢ a) → elimIsolated a ≡ neq* (a , ¬p)
  elimIsolated-β-no a ¬p i = Dec.elim (eq* a) (λ neq → neq* (a , neq)) (isIsolated→isPropDecPath a₀ a₀≟_ a (a₀≟ a) (no ¬p) i)

Isolated≡ : ∀ {a b : A °} → a .fst ≡ b .fst → a ≡ b
Isolated≡ = Σ≡Prop isPropIsIsolated

Isolated≢ : ∀ {a b : A °} → a .fst ≢ b .fst → a ≢ b
Isolated≢ a≢b p = a≢b $ cong fst p

DiscreteIsolated : Discrete (Isolated A)
DiscreteIsolated (a , a≟_) (b , b≟_) = Dec.map Isolated≡ Isolated≢ (a≟ b)

opaque
  isSetIsolated : isSet (A °)
  isSetIsolated = Dec.Discrete→isSet DiscreteIsolated

module _ (_≟_ : Discrete A) where
  Discrete→isIsolated : ∀ a → isIsolated a
  Discrete→isIsolated = _≟_

  Discrete→IsolatedEquiv : A ° ≃ A
  Discrete→IsolatedEquiv = Σ-contractSnd λ a → inhProp→isContr (Discrete→isIsolated a) (isPropIsIsolated a)

opaque
  isIsolatedRespectEquiv : (e : A ≃ B) → (b : B) → isIsolated b → isIsolated (invEq e b)
  isIsolatedRespectEquiv e b isolated a = EquivPresDec eqv (isolated (equivFun e a))
    where
      eqv : (b ≡ equivFun e a) ≃ (invEq e b ≡ a)
      eqv = symEquiv ∙ₑ invEquiv (equivAdjointEquiv e) ∙ₑ symEquiv

opaque
  isIsolatedFromEmbedding : (f : A → B) → isEmbedding f → ∀ {a} → isIsolated (f a) → isIsolated a
  isIsolatedFromEmbedding f emb-f {a} isolated-fa a′ =
    Dec.map
      (isEmbedding→Inj emb-f a a′)
      (λ fa≢fa′ a≡a′ → fa≢fa′ $ cong f a≡a′)
      (isolated-fa (f a′))

isIsolatedFromInl : ∀ {a : A} → isIsolated (inl {B = B} a) → isIsolated a
isIsolatedFromInl = isIsolatedFromEmbedding inl Sum.isEmbedding-inl

isIsolatedFromInr : ∀ {b : B} → isIsolated (inr {A = A} b) → isIsolated b
isIsolatedFromInr = isIsolatedFromEmbedding inr Sum.isEmbedding-inr

isIsolatedInl : ∀ {a : A} → isIsolated a → isIsolated (inl {B = B} a)
isIsolatedInl {a} isolated-a (inl a′) = Dec.decEquiv (cong inl , Sum.isEmbedding-inl a a′) (isolated-a a′)
isIsolatedInl {a} isolated-a (inr b) = no λ inl≡inr → Sum.⊎Path.encode _ _ inl≡inr .lower

isIsolatedInr : ∀ {b : B} → isIsolated b → isIsolated (inr {A = A} b)
isIsolatedInr {b} isolated-b (inl a) = no λ inr≡inl → Sum.⊎Path.encode _ _ inr≡inl .lower
isIsolatedInr {b} isolated-b (inr b′) = Dec.decEquiv (cong inr , Sum.isEmbedding-inr b b′) (isolated-b b′)

opaque
  isIsolatedTransport : (a : A) (p : A ≡ B) → isIsolated a → isIsolated (transport p a)
  isIsolatedTransport a = J (λ B p → isIsolated a → isIsolated (transport p a)) λ where
    isolated-a a′ → subst (λ - → Dec (- ≡ a′)) (sym $ transportRefl a) (isolated-a a′)

isProp→isIsolated : isProp A → (a : A) → isIsolated a
isProp→isIsolated prop-A a b = yes $ prop-A a b

isContr→isIsolatedCenter : isContr A → (a : A) → isIsolated a
isContr→isIsolatedCenter = isProp→isIsolated ∘ isContr→isProp

remove-emb : (a : A) → A ∖ a → A
remove-emb a = fst

-- isIsolatedΣ : ∀ {ℓB} {B : A → Type ℓB}
--   → {a : A} {b : B a}
--   → isIsolated {A = Σ A B} (a , b) ≃ (isIsolated a × isIsolated b)
-- isIsolatedΣ {B} {a} {b} = propBiimpl→Equiv (isPropIsIsolated _) (isProp× (isPropIsIsolated _) (isPropIsIsolated _))
--   (λ isolated-ab → (λ { a′ → {! isolated-ab (a′ , ?) !} }) , {! !})
--   (λ { (isolated-a , isolated-b) (a′ , b′) → {!discreteΣ !} })

isIsolatedΣ : ∀ {ℓB} {B : A → Type ℓB}
  → {a : A} {b : B a}
  → isIsolated a
  → isIsolated b
  → isIsolated {A = Σ A B} (a , b)
isIsolatedΣ {B} {a} {b} isolated-a isolated-b (a′ , b′) = discrete (isolated-a a′) where
  discrete : Dec (a ≡ a′) → Dec ((a , b) ≡ (a′ , b′))
  discrete (yes p) = Dec.decEquiv (ΣPathTransport≃PathΣ _ _) (discrete-b (isolated-b _)) where
    adj : {p : a ≡ a′} → (subst B p b ≡ b′) ≃ (b ≡ subst B (sym p) b′)
    adj {p} = substAdjointEquiv B p

    discrete-b : Dec (b ≡ subst B (sym p) b′) → Dec (Σ[ p ∈ a ≡ a′ ] subst B p b ≡ b′)
    discrete-b (yes q) = yes (p , invEq adj q)
    discrete-b (no ¬q) = no λ { (p , q) → ¬q (equivFun adj $ cong (λ - → subst B - b) (isIsolated→isPropPath a isolated-a a′ _ _) ∙ q) }
    
  discrete (no ¬p) = no λ r → ¬p (cong fst r)

Σ-isolate : ∀ {ℓA ℓB} (A : Type ℓA) (B : A → Type ℓB)
  → (Σ[ a° ∈ A ° ] (B (a° .fst)) °) → (Σ[ a ∈ A ] B a) °
Σ-isolate A B ((a , isolated-a) , b , isolated-b) .fst = a , b
Σ-isolate A B ((a , isolated-a) , b , isolated-b) .snd = isIsolatedΣ isolated-a isolated-b

isIsolatedΣSnd→Discrete : {ℓ : Level}
  → (A : Type ℓ)
  → ((a₀ : A) → (B : A → Type ℓ) → (b₀ : B a₀) → isIsolated {A = Σ A B} (a₀ , b₀) → isIsolated a₀)
  → Discrete A
isIsolatedΣSnd→Discrete {ℓ} A Σ-isolated-fst a₀ a₁ = goal where
  B' : A → Type ℓ
  B' a = a₀ ≡ a

  b₀ : B' a₀
  b₀ = refl

  is-isolated-pair : isIsolated {A = Σ A B'} (a₀ , b₀)
  is-isolated-pair = isContr→isIsolatedCenter (isContrSingl a₀) (a₀ , b₀)

  goal : Dec (a₀ ≡ a₁)
  goal = Σ-isolated-fst a₀ B' b₀ is-isolated-pair a₁

isEquiv-Σ-isolate→DiscreteFst : (A : Type ℓ)
  → ((B : A → Type ℓ) → isEquiv (Σ-isolate A B))
  → Discrete A
isEquiv-Σ-isolate→DiscreteFst A is-equiv-Σ-isolate = isIsolatedΣSnd→Discrete A goal where
  unisolate : (B : A → Type _) → (Σ[ a ∈ A ] B a) ° → (Σ[ a° ∈ A ° ] (B (a° .fst)) °)
  unisolate B = invIsEq (is-equiv-Σ-isolate B)

  unisolate-β-fst : (B : A → Type _) → {a : A} → {b : B a} → (isolated-ab : isIsolated (a , b))
    → unisolate B ((a , b) , isolated-ab) .fst .fst ≡ a
  unisolate-β-fst B {a} {b} isolated-ab = sym (cong (fst ∘ fst) (invEq (equivAdjointEquiv (_ , is-equiv-Σ-isolate B)) (Isolated≡ refl)))

  goal : ∀ a₀ (B : A → Type _) (b₀ : B a₀) → isIsolated (a₀ , b₀) → isIsolated a₀
  goal a₀ B b₀ isolated-ab = subst isIsolated (unisolate-β-fst B isolated-ab) (unisolate B (_ , isolated-ab) .fst .snd)

Discrete→isEquiv-Σ-isolate : {A : Type ℓ} {B : A → Type ℓ}
  → Discrete A
  → (∀ a → Discrete (B a))
  → isEquiv (Σ-isolate A B)
Discrete→isEquiv-Σ-isolate {A} {B} disc-A disc-B = subst isEquiv compute (equivIsEquiv e) where
  e : (Σ[ a° ∈ A ° ] (B (a° .fst)) °) ≃ ((Σ[ a ∈ A ] B a) °)
  e =
    Σ[ a° ∈ A ° ] (B (a° .fst)) °
      ≃⟨ Σ-cong-equiv (Discrete→IsolatedEquiv disc-A) (Discrete→IsolatedEquiv ∘ disc-B ∘ fst) ⟩
    Σ[ a ∈ A ] B a
      ≃⟨ invEquiv (Discrete→IsolatedEquiv (discreteΣ disc-A disc-B)) ⟩
    (Σ[ a ∈ A ] B a) °
      ≃∎

  compute : equivFun e ≡ Σ-isolate A B
  compute = funExt λ _ → Isolated≡ refl

isPerfect : (A : Type ℓ) → Type ℓ
isPerfect A = ¬ (A °)


stitch : (a° : A °) → (((A ∖ a° .fst) → B) × B) → (A → B)
stitch a° (f , b₀) = elimIsolated a° (λ _ _ → b₀) f

stitch-β : (a° : A °) (f : (A ∖ a° .fst) → B) {b₀ : B} → stitch a° (f , b₀) (a° .fst) ≡ b₀
stitch-β a° f {b₀} = elimIsolated-β-refl a° (λ _ _ → b₀) f

unstitch : (a° : A °) → (A → B) → (((A ∖ a° .fst) → B) × B)
unstitch (a₀ , _) f .fst = f ∘ fst
unstitch (a₀ , _) f .snd = f a₀

isEquivStitch : (a° : A °) → isEquiv (stitch {B = B} a°)
isEquivStitch {A} {B} a°@(a₀ , a₀≟_) = isoToIsEquiv stich-iso module isEquivStitch where

  stich-iso : Iso (((A ∖ a₀) → B) × B) (A → B)
  stich-iso .Iso.fun = stitch a°
  stich-iso .Iso.inv = unstitch a°
  stich-iso .Iso.rightInv f = funExt λ a → goal a (a₀≟ a) where
    goal : (a : A) → Dec (a₀ ≡ a) → stitch a° (unstitch a° f) a ≡ f a
    goal a (yes p) = elimIsolated-β-yes a° (λ _ _ → f a₀) (f ∘ fst) a p ∙ cong f p
    goal a (no ¬p) = elimIsolated-β-no a° (λ _ _ → f a₀) (f ∘ fst) a ¬p
  stich-iso .Iso.leftInv (f° , b) = ΣPathP λ where
    .fst → funExt λ (a , a₀≢a) → elimIsolated-β-no a° (λ _ _ → b) f° a a₀≢a
    .snd → elimIsolated-β-refl a° (λ _ _ → b) f°

stitchEquiv : (a° : A °) → ((A ∖ a° .fst → B) × B) ≃ (A → B)
stitchEquiv a° .fst = stitch a°
stitchEquiv a° .snd = isEquivStitch a°

unstitchEquiv : (a° : A °) → (A → B) ≃ ((A ∖ a° .fst → B) × B)
unstitchEquiv a° .fst = unstitch a°
unstitchEquiv a° .snd = isoToIsEquiv $ invIso $ isEquivStitch.stich-iso _ (a° .snd)

module S1 where
  open import Cubical.HITs.S1
  open import Cubical.Data.Int

  private
    S¹-elimProp : ∀ {ℓP} {P : S¹ → Type ℓP}
      → (∀ x → isProp (P x))
      → P base
      → ∀ x → P x
    S¹-elimProp {P = P} is-prop-P base* base = base*
    S¹-elimProp {P = P} is-prop-P base* (loop i) = isProp→PathP (λ i → is-prop-P (loop i)) base* base* i

    refl≢loop : refl ≢ loop
    refl≢loop refl≡loop = 0≢1-ℤ (cong winding refl≡loop)

  isIsolatedBase→isPropBaseLoop : isIsolated base → isProp (base ≡ base)
  isIsolatedBase→isPropBaseLoop isolated-base p q = isEmbedding→Inj Dec.isEmbeddingYes p q yes-path where
    dec-base≡ : Dec (base ≡ base)
    dec-base≡ = isolated-base base

    is-prop-dec-base≡ : isProp (Dec (base ≡ base))
    is-prop-dec-base≡ = isIsolated→isPropDecPath base isolated-base base

    yes-path : yes p ≡ yes q
    yes-path = is-prop-dec-base≡ (yes p) (yes q)

  ¬isIsolated-base : ¬ isIsolated base
  ¬isIsolated-base isolated-base = refl≢loop (isIsolatedBase→isPropBaseLoop isolated-base refl loop)

  isPerfectS¹ : isPerfect S¹
  isPerfectS¹ = uncurry (S¹-elimProp (λ x → Dec.isProp¬ (isIsolated x)) ¬isIsolated-base)
