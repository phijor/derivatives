{-# OPTIONS -WnoUnsupportedIndexedMatch --safe #-}
module Derivative.Isolated.Base where

open import Derivative.Prelude
open import Derivative.Basics.Decidable
  as Dec
  using
    ( locallyDiscrete→locallyIsPropPath
    ; Dec ; yes ; no
    ; Discrete
    ; isProp¬
    )
open import Derivative.Basics.Embedding
open import Derivative.Basics.Sigma
open import Derivative.Basics.Sum as Sum using (_⊎_ ; inl ; inr)
open import Derivative.Basics.W as W
open import Derivative.Remove

open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv ; hasRetract ; hasSection ; congEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (toPathP⁻ ; flipSquare)
open import Cubical.Foundations.Transport using (subst⁻ ; subst⁻-filler)
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Relation.Nullary.Properties using (EquivPresDec ; EquivPresDiscrete)
open import Cubical.Relation.Nullary.HLevels using (isPropDiscrete)
open import Cubical.Data.Unit as Unit using (Unit*)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

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

forget-isolated : A ° → A
forget-isolated = fst

_-_ : (A : Type ℓ) (a : A °) → Type ℓ
A - a = A ∖ (a .fst)

isIsolated→K : (a : A °) (p : a .fst ≡ a .fst) → p ≡ refl
isIsolated→K (a , is-isolated-a) p = isIsolated→isPropPath a is-isolated-a a p refl

isIsolated→isContrLoop : (a : A) → isIsolated a → isContr (a ≡ a)
isIsolated→isContrLoop a is-isolated-a .fst = refl
isIsolated→isContrLoop a is-isolated-a .snd = sym ∘ isIsolated→K (a , is-isolated-a)


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

IsolatedPathP : ∀ {B : A → Type ℓ} {a₀ a₁ : A} {p : a₀ ≡ a₁}
  → {b₀ : B a₀ °} {b₁ : B a₁ °}
  → PathP (λ i → B (p i)) (b₀ .fst) (b₁ .fst)
  → PathP (λ i → B (p i) °) b₀ b₁
IsolatedPathP q i .fst = q i
IsolatedPathP {b₀} {b₁} q i .snd = isProp→PathP {B = λ i → isIsolated (q i)} (λ i → isPropIsIsolated (q i)) (b₀ .snd) (b₁ .snd) i

Isolated≢ : ∀ {a b : A °} → a .fst ≢ b .fst → a ≢ b
Isolated≢ a≢b p = a≢b $ cong fst p

DiscreteIsolated : Discrete (Isolated A)
DiscreteIsolated (a , a≟_) (b , b≟_) = Dec.map Isolated≡ Isolated≢ (a≟ b)

opaque
  isSetIsolated : isSet (A °)
  -- isSetIsolated = Dec.Discrete→isSet DiscreteIsolated
  isSetIsolated (a₀ , isolated-a₀) (a₁ , isolated-a₁) = isOfHLevelRespectEquiv 1 ΣPathP≃PathPΣ $ isPropΣ
    (isIsolated→isPropPath a₀ isolated-a₀ a₁)
    (λ p → isOfHLevelPathP 1 (isPropIsIsolated a₁) _ _)

module _ (_≟_ : Discrete A) where
  Discrete→isIsolated : ∀ a → isIsolated a
  Discrete→isIsolated = _≟_

  Discrete→isEquiv-forget-isolated : isEquiv {A = A °} forget-isolated
  Discrete→isEquiv-forget-isolated = equivIsEquiv $ Σ-contractSnd λ a → inhProp→isContr (Discrete→isIsolated a) (isPropIsIsolated a)

  Discrete→IsolatedEquiv : A ° ≃ A
  Discrete→IsolatedEquiv .fst = forget-isolated
  Discrete→IsolatedEquiv .snd = Discrete→isEquiv-forget-isolated

isEquiv-forget-isolated→Discrete : isEquiv {A = A °} forget-isolated → Discrete A
isEquiv-forget-isolated→Discrete is-equiv-forget = EquivPresDiscrete (forget-isolated , is-equiv-forget) DiscreteIsolated

isEquiv-forget-isolated≃Discrete : isEquiv {A = A °} forget-isolated ≃ Discrete A
isEquiv-forget-isolated≃Discrete = propBiimpl→Equiv (isPropIsEquiv _) isPropDiscrete
  isEquiv-forget-isolated→Discrete
  Discrete→isEquiv-forget-isolated

opaque
  isIsolatedRespectEquiv : (e : A ≃ B) → (b : B) → isIsolated b → isIsolated (invEq e b)
  isIsolatedRespectEquiv e b isolated a = EquivPresDec eqv (isolated (equivFun e a))
    where
      eqv : (b ≡ equivFun e a) ≃ (invEq e b ≡ a)
      eqv = symEquiv ∙ₑ invEquiv (equivAdjointEquiv e) ∙ₑ symEquiv

  isIsolatedPreserveEquiv : (e : A ≃ B) → (a : A) → isIsolated a → isIsolated (equivFun e a)
  isIsolatedPreserveEquiv e a isolated b = EquivPresDec (equivAdjointEquiv e) (isolated (invEq e b))

  isIsolatedPreserveEquiv' : (e : A ≃ B) → (a : A) → isIsolated (equivFun e a) → isIsolated a
  isIsolatedPreserveEquiv' e a isolated a′ = EquivPresDec (invEquiv (congEquiv e)) (isolated (equivFun e a′))

IsolatedSubstEquiv : (e : A ≃ B) → A ° ≃ B °
IsolatedSubstEquiv e = Σ-cong-equiv e lemma where
  lemma : ∀ a → isIsolated a ≃ isIsolated (equivFun e a)
  lemma a = propBiimpl→Equiv (isPropIsIsolated _) (isPropIsIsolated _) (isIsolatedPreserveEquiv e a) (isIsolatedPreserveEquiv' e a)

opaque
  InjReflectIsolated : (f : A → B) → (∀ a b → f a ≡ f b → a ≡ b) → ∀ {a} → isIsolated (f a) → isIsolated a
  InjReflectIsolated f inj-f {a} isolated-fa a′ =
    Dec.map
      (inj-f a a′)
      (λ fa≢fa′ a≡a′ → fa≢fa′ $ cong f a≡a′)
      (isolated-fa (f a′))

  EmbeddingReflectIsolated : (f : A → B) → isEmbedding f → ∀ {a} → isIsolated (f a) → isIsolated a
  EmbeddingReflectIsolated f emb-f = InjReflectIsolated f (isEmbedding→Inj emb-f)

  EmbeddingReflectIsolated' : (f : A → B) → isEmbedding f → ∀ {a} → isIsolated (f a) → isIsolated a
  EmbeddingReflectIsolated' f emb-f {a} isolated-fa a′ = EquivPresDec (invEquiv $ cong f , emb-f a a′) (isolated-fa (f a′))

  DecEmbeddingCreateIsolated : (f : A → B) → isEmbedding f → (∀ b → Dec (fiber f b)) → ∀ {a} → isIsolated a → isIsolated (f a)
  DecEmbeddingCreateIsolated f emb-f dec-fib {a} isolated-a b with (dec-fib b)
  ... | (yes (a′ , fa′≡b)) = Dec.map (λ a≡a′ → cong f a≡a′ ∙ fa′≡b) (λ a≢a′ fa≡b → a≢a′ (isEmbedding→Inj emb-f _ _ (fa≡b ∙ sym fa′≡b))) (isolated-a a′)
  ... | (no ¬fib) = no (¬fib ∘ (a ,_))

opaque
  isIsolatedTransport : (a : A) (p : A ≡ B) → isIsolated a → isIsolated (transport p a)
  isIsolatedTransport a = J (λ B p → isIsolated a → isIsolated (transport p a)) λ where
    isolated-a a′ → subst (λ - → Dec (- ≡ a′)) (sym $ transportRefl a) (isolated-a a′)

  isIsolatedSubst : (B : A → Type ℓ) {x y : A} (p : x ≡ y)
    → {b : B x}
    → isIsolated b
    → isIsolated (subst B p b)
  isIsolatedSubst B p {b} = isIsolatedTransport b (cong B p)

subst° : (B : A → Type ℓ) {x y : A} (p : x ≡ y) → B x ° → B y °
subst° B p (b , isolated-b) .fst = subst B p b
subst° B p (b , isolated-b) .snd = isIsolatedSubst B p isolated-b

isProp→isIsolated : isProp A → (a : A) → isIsolated a
isProp→isIsolated prop-A a b = yes $ prop-A a b

isProp→IsolatedEquiv : ∀ {P : Type ℓ} → isProp P → (P °) ≃ P
isProp→IsolatedEquiv = Discrete→IsolatedEquiv ∘ Dec.isProp→Discrete

isContr→isIsolatedCenter : isContr A → (a : A) → isIsolated a
isContr→isIsolatedCenter = isProp→isIsolated ∘ isContr→isProp

remove-emb : (a : A) → A ∖ a → A
remove-emb a = fst

-- Yeah, that's a pity:
DecIsolated→DecProp : (∀ (A : Type ℓ) → Dec (Isolated A)) → ∀ P → isProp P → Dec P
DecIsolated→DecProp all-dec P is-prop-P = Dec.map forget-isolated nope (all-dec P)
  where
    nope : ¬ (P °) → ¬ P
    nope heck-no p = heck-no (invEq (isProp→IsolatedEquiv is-prop-P) p)

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
    discrete-b (no ¬q) = no λ { (p , q) → ¬q (equivFun adj $ cong (λ p → subst B p b) (isIsolated→isPropPath a isolated-a a′ _ _) ∙ q) }
    
  discrete (no ¬p) = no λ r → ¬p (cong fst r)

Σ-isolate : ∀ {ℓA ℓB} (A : Type ℓA) (B : A → Type ℓB)
  → (Σ[ a° ∈ A ° ] (B (a° .fst)) °) → (Σ[ a ∈ A ] B a) °
Σ-isolate A B ((a , isolated-a) , b , isolated-b) .fst .fst = a
Σ-isolate A B ((a , isolated-a) , b , isolated-b) .fst .snd = b
Σ-isolate A B ((a , isolated-a) , b , isolated-b) .snd = isIsolatedΣ isolated-a isolated-b

_,°_ : ∀ {B : A → Type ℓ} (a : A °) (b : B (a .fst) °) → (Σ[ a ∈ A ] B a) °
a ,° b = Σ-isolate _ _ (a , b)

isIsolatedΣSndProp : ∀ {ℓP} {P : A → Type ℓP}
  → {a : A} {p : P a}
  → isIsolated a
  → isProp (P a)
  → isIsolated {A = Σ A P} (a , p)
isIsolatedΣSndProp {P} {a} {p} isolated-a is-prop-P = isIsolatedΣ isolated-a (isProp→isIsolated is-prop-P p)

isIsolatedΣSnd→Discrete : {ℓ : Level}
  → (A : Type ℓ)
  → ((B : A → Type ℓ) → (a₀ : A) → (b₀ : B a₀) → isIsolated {A = Σ A B} (a₀ , b₀) → isIsolated a₀)
  → Discrete A
isIsolatedΣSnd→Discrete {ℓ} A Σ-isolated-fst a₀ a₁ = goal where
  B' : A → Type ℓ
  B' a = a₀ ≡ a

  b₀ : B' a₀
  b₀ = refl

  is-isolated-pair : isIsolated {A = Σ A B'} (a₀ , b₀)
  is-isolated-pair = isContr→isIsolatedCenter (isContrSingl a₀) (a₀ , b₀)

  goal : Dec (a₀ ≡ a₁)
  goal = Σ-isolated-fst B' a₀ b₀ is-isolated-pair a₁

module _ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} (is-equiv-Σ-isolate : isEquiv (Σ-isolate A B)) where
  private
    unisolate-equiv : (Σ[ a ∈ A ] B a) ° ≃ (Σ[ a° ∈ A ° ] (B (a° .fst)) °)
    unisolate-equiv = invEquiv (_ , is-equiv-Σ-isolate)

    unisolate : (Σ[ a ∈ A ] B a) ° → (Σ[ a° ∈ A ° ] (B (a° .fst)) °)
    unisolate = equivFun unisolate-equiv

  isEquiv-Σ-isolate→isIsolatedPair : {a₀ : A} {b₀ : B a₀} → isIsolated {A = Σ A B} (a₀ , b₀) → isIsolated a₀ × isIsolated b₀
  isEquiv-Σ-isolate→isIsolatedPair {a₀} {b₀} isolated-ab
    using ab°@((a , isolated-a) , (b , isolated-b)) ← unisolate ((a₀ , b₀) , isolated-ab)
    = isolated-a₀ , isolated-b₀ where
      help : Σ-isolate A B ab° ≡ Σ-isolate A B (unisolate ((a₀ , b₀) , isolated-ab))
      help = Isolated≡ $ refl′ (a , b)

      fib₀ : fiber unisolate ab°
      fib₀ .fst = Σ-isolate A B ab°
      fib₀ .snd = sym (invEq (equivAdjointEquiv (_ , is-equiv-Σ-isolate)) help)

      fib₁ : fiber unisolate ab°
      fib₁ .fst = (a₀ , b₀) , isolated-ab
      fib₁ .snd = refl

      contr-fib = equivIsEquiv unisolate-equiv .equiv-proof ab°

      fib₀≡fib₁ : fib₀ ≡ fib₁
      fib₀≡fib₁ = isContr→isProp contr-fib _ _

      a≡a₀ : a ≡ a₀
      a≡a₀ = cong (fst ∘ fst ∘ fst) fib₀≡fib₁

      isolated-a₀ : isIsolated a₀
      isolated-a₀ = subst isIsolated a≡a₀ isolated-a

      b≡b₀ : PathP (λ i → B (a≡a₀ i)) b b₀
      b≡b₀ = cong (snd ∘ fst ∘ fst) fib₀≡fib₁

      isolated-b₀ : isIsolated b₀
      isolated-b₀ = transport (λ i → (b : B (a≡a₀ i)) → Dec (b≡b₀ i ≡ b)) isolated-b

  isEquiv-Σ-isolate→isIsolatedFst : {a₀ : A} {b₀ : B a₀} → isIsolated {A = Σ A B} (a₀ , b₀) → isIsolated a₀
  isEquiv-Σ-isolate→isIsolatedFst = fst ∘ isEquiv-Σ-isolate→isIsolatedPair

isIsolatedPair→isEquiv-Σ-isolated : {A : Type ℓ} {B : A → Type ℓ}
  → (∀ {a₀ : A} {b₀ : B a₀} → isIsolated {A = Σ A B} (a₀ , b₀) → isIsolated a₀ × isIsolated b₀)
  → isEquiv (Σ-isolate A B)
isIsolatedPair→isEquiv-Σ-isolated {A} {B} is-isolated-pair = isoToIsEquiv Σ-isolate-Iso where
  Σ-isolate⁻¹ : (Σ[ a ∈ A ] B a) ° → (Σ[ a° ∈ A ° ] (B (a° .fst)) °)
  Σ-isolate⁻¹ ((a , b) , isolated-ab)
    using (isolated-a , isolated-b) ← is-isolated-pair isolated-ab
    = (a , isolated-a) , (b , isolated-b)

  Σ-isolate-Iso : Iso (Σ[ a° ∈ A ° ] (B (a° .fst)) °) ((Σ[ a ∈ A ] B a) °)
  Σ-isolate-Iso .Iso.fun = Σ-isolate A B
  Σ-isolate-Iso .Iso.inv = Σ-isolate⁻¹
  Σ-isolate-Iso .Iso.rightInv _ = Isolated≡ refl
  Σ-isolate-Iso .Iso.leftInv _ = ΣPathP (Isolated≡ refl , Isolated≡ refl)

Σ-isolate-fiber-equiv : ∀ (A : Type ℓ) (B : A → Type ℓ)
  → (a : A) (b : B a) (isolated-ab : isIsolated {A = Σ A B} (a , b))
  → fiber (Σ-isolate A B) ((a , b) , isolated-ab) ≃ (isIsolated a × isIsolated b)
Σ-isolate-fiber-equiv A B a b isolated-ab =
  (Σ[ ((a′ , _) , (b′ , _)) ∈ Σ[ (a , _) ∈ A ° ] B a ° ] ((a′ , b′) , _) ≡ _)
    ≃⟨ Σ-cong-equiv-snd (λ _ → invEquiv $ Σ≡PropEquiv isPropIsIsolated) ⟩
  (Σ[ ((a′ , _) , (b′ , _)) ∈ Σ[ (a , _) ∈ A ° ] B a ° ] (a′ , b′) ≡ (a , b))
    ≃⟨ Σ-cong-equiv-snd (λ _ → invEquiv ΣPathP≃PathPΣ) ⟩
  (Σ[ ((a′ , _) , (b′ , _)) ∈ Σ[ (a , _) ∈ A ° ] B a ° ] Σ[ p ∈ a′ ≡ a ] PathP (λ i → B (p i)) b′ b)
    ≃⟨ strictEquiv
      (λ { (((a′ , h-a′) , (b′ , h-b′)) , p , pᴰ) → ((a′ , sym p) , (b′ , symP pᴰ) , (h-a′ , h-b′)) })
      (λ { ((a′ , p) , (b′ , pᴰ) , (h-a′ , h-b′)) → (((a′ , h-a′) , (b′ , h-b′)) , sym p , symP pᴰ) })
    ⟩
  (Σ[ (a′ , p) ∈ singl a ] Σ[ (b′ , pᴰ) ∈ singlP (λ i → B (p i)) b ] isIsolated a′ × isIsolated b′)
    ≃⟨ Σ-contractFst (isContrSingl a) ⟩
  (Σ[ (b′ , pᴰ) ∈ singl b ] isIsolated a × isIsolated b′)
    ≃⟨ Σ-contractFst (isContrSingl b) ⟩
  (isIsolated a × isIsolated b)
    ≃∎

isProp-fiber-Σ-isolate : ∀ (A : Type ℓ) (B : A → Type ℓ)
  → ∀ y → isProp (fiber (Σ-isolate A B) y)
isProp-fiber-Σ-isolate A B y = isOfHLevelRespectEquiv 1 (invEquiv $ Σ-isolate-fiber-equiv A B _ _ _)
  $ isProp× (isPropIsIsolated _) (isPropIsIsolated _)

isEmbedding-Σ-Isolate : ∀ (A : Type ℓ) (B : A → Type ℓ) → isEmbedding (Σ-isolate A B)
isEmbedding-Σ-Isolate A B = hasPropFibers→isEmbedding $ isProp-fiber-Σ-isolate A B

Σ-isolate-embedding : ∀ (A : Type ℓ) (B : A → Type ℓ)
  → (Σ[ a° ∈ A ° ] (B (a° .fst)) °) ↪ ((Σ[ a ∈ A ] B a) °)
Σ-isolate-embedding A B .fst = Σ-isolate A B
Σ-isolate-embedding A B .snd = isEmbedding-Σ-Isolate A B

isEquiv-Σ-isolate≃isSurjection-Σ-isolate : (A : Type ℓ) (B : A → Type ℓ) → isEquiv (Σ-isolate A B) ≃ isSurjection (Σ-isolate A B)
isEquiv-Σ-isolate≃isSurjection-Σ-isolate A B =
  isEquiv _
    ≃⟨ isEquiv≃isEquiv' _ ⟩
  (∀ y → isContr (fiber (Σ-isolate A B) y))
    ≃⟨ equivΠCod (λ y → isContr≃mereInh×isProp) ⟩
  (∀ y → ∥ fiber _ y ∥₁ × isProp (fiber _ y))
    ≃⟨ equivΠCod (λ y → Σ-contractSnd λ _ → inhProp→isContr (isProp-fiber-Σ-isolate _ _ y) isPropIsProp) ⟩
  (∀ y → ∥ fiber _ y ∥₁)
    ≃∎

isSurjection-Σ-isolate≃isIsolatedPair : (A : Type ℓ) (B : A → Type ℓ)
  → isSurjection (Σ-isolate A B) ≃ (∀ a → (b : B a) → isIsolated {A = Σ A B} (a , b) → isIsolated a × isIsolated b)
isSurjection-Σ-isolate≃isIsolatedPair A B =
  (∀ y → ∥ fiber _ y ∥₁)
    ≃⟨ equivΠCod (λ y → PT.propTruncIdempotent≃ (isProp-fiber-Σ-isolate _ _ y))  ⟩
  (∀ y → fiber _ y)
    ≃⟨ curryEquiv ⟩
  ((a,b : Σ A B) → (h : isIsolated a,b) → fiber (Σ-isolate A B) (a,b , h))
    ≃⟨ curryEquiv ⟩
  ((a : A) (b : B a) (h : isIsolated (a , b)) → fiber (Σ-isolate A B) ((a , b) , h))
    ≃⟨ equivΠCod (λ a → equivΠCod λ b → equivΠCod λ h → Σ-isolate-fiber-equiv A B a b h) ⟩
  ((a : A) (b : B a) → isIsolated (a , b) → isIsolated a × isIsolated b)
    ≃∎

isEquiv-Σ-isolate≃isIsolatedPair : (A : Type ℓ) (B : A → Type ℓ)
 → isEquiv (Σ-isolate A B) ≃ (∀ (a₀ : A) (b₀ : B a₀) → isIsolated {A = Σ A B} (a₀ , b₀) → isIsolated a₀ × isIsolated b₀)
isEquiv-Σ-isolate≃isIsolatedPair A B = isEquiv-Σ-isolate≃isSurjection-Σ-isolate A B ∙ₑ isSurjection-Σ-isolate≃isIsolatedPair A B

isIsolated→isEmbeddingInjSnd : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB}
  → (a₀ : A) → isIsolated a₀
  → isEmbedding {A = B a₀} {B = Σ A B} (a₀ ,_)
isIsolated→isEmbeddingInjSnd {A} {B} a₀ is-isolated-a₀ = λ b₀ b₁ → equivIsEquiv $ isoToEquiv (path-iso b₀ b₁) where
  path-iso : (b₀ b₁ : B a₀) → Iso (b₀ ≡ b₁) ((a₀ , b₀) ≡ (a₀ , b₁))
  path-iso b₀ b₁ =
    (b₀ ≡ b₁)
      Iso⟨ invIso (Σ-contractFstIso (isIsolated→isContrLoop a₀ is-isolated-a₀)) ⟩
    Σ[ p ∈ a₀ ≡ a₀ ] PathP (λ i → B (p i)) b₀ b₁
      Iso⟨ ΣPathPIsoPathPΣ {B = λ i → B} ⟩
    ((a₀ , b₀) ≡ (a₀ , b₁))
      ∎Iso

isIsolatedFst→isIsolatedSnd≃isIsolatedPair : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB}
  → {a₀ : A} → isIsolated a₀
  → (b₀ : B a₀)
  → isIsolated b₀ ≃ isIsolated {A = Σ A B} (a₀ , b₀)
isIsolatedFst→isIsolatedSnd≃isIsolatedPair {A} {B} {a₀} isolated-a₀ b₀ = propBiimpl→Equiv
  (isPropIsIsolated b₀)
  (isPropIsIsolated (a₀ , b₀))
  (isIsolatedΣ isolated-a₀)
  (EmbeddingReflectIsolated (a₀ ,_) $ isIsolated→isEmbeddingInjSnd a₀ isolated-a₀)

isEquiv-Σ-isolate→DiscreteFst : (A : Type ℓ)
  → ((B : A → Type ℓ) → isEquiv (Σ-isolate A B))
  → Discrete A
isEquiv-Σ-isolate→DiscreteFst {ℓ} A is-equiv-Σ-isolate = isIsolatedΣSnd→Discrete A goal where
  goal : ∀ (B : A → Type ℓ) a₀ (b₀ : B a₀) → isIsolated (a₀ , b₀) → isIsolated a₀
  goal B a₀ b₀ isolated-ab = isEquiv-Σ-isolate→isIsolatedFst (is-equiv-Σ-isolate B) isolated-ab

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

Discrete→isEquiv-Σ-isolate-singl : Discrete A → (a₀ : A) → isEquiv (Σ-isolate A (a₀ ≡_))
Discrete→isEquiv-Σ-isolate-singl {A} disc-A a₀ = Discrete→isEquiv-Σ-isolate disc-A disc-a₀≡a where
  disc-a₀≡a : (a : A) → Discrete (a₀ ≡ a)
  disc-a₀≡a = Dec.Discrete→DiscretePath disc-A a₀

isEquiv-Σ-isolate-singl→Discrete : (∀ a₀ → isEquiv (Σ-isolate A (a₀ ≡_))) → Discrete A
isEquiv-Σ-isolate-singl→Discrete is-equiv-Σ-isolate a₀ = isolated-a₀ where
  is-isolated-center : isIsolated {A = singl a₀} (a₀ , refl)
  is-isolated-center = isContr→isIsolatedCenter (isContrSingl a₀) (a₀ , refl)

  isolated-a₀ : isIsolated a₀
  isolated-a₀ = isEquiv-Σ-isolate→isIsolatedFst (is-equiv-Σ-isolate a₀) is-isolated-center

Discrete≃isEquiv-Σ-isolate-singl : Discrete A ≃ ((a₀ : A) → isEquiv (Σ-isolate A (a₀ ≡_)))
Discrete≃isEquiv-Σ-isolate-singl = propBiimpl→Equiv
  isPropDiscrete
  (isPropΠ λ a₀ → isPropIsEquiv _)
  Discrete→isEquiv-Σ-isolate-singl
  isEquiv-Σ-isolate-singl→Discrete

module _ {B : A → Type ℓ} {a₀ : A} {b₀ : B a₀}
  (a₀≟_ : isIsolated a₀)
  where
  private
    is-prop-a₀-loop : isProp (a₀ ≡ a₀)
    is-prop-a₀-loop = isIsolated→isPropPath a₀ a₀≟_ a₀

    Σ-remove' = Σ-remove {B = B} a₀ b₀ is-prop-a₀-loop

    Σ-remove-inv' : ∀ a → Dec (a₀ ≡ a) → (b : B a) → (a₀ , b₀) ≢ (a , b) → (Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀)
    Σ-remove-inv' a (yes a₀≡a) b neq = on-yes where
      b₀≢subst-b : b₀ ≢ subst⁻ B a₀≡a b
      b₀≢subst-b q = neq goal where
        b₀≡ᴰb : PathP (λ i → B (a₀≡a i)) b₀ b
        b₀≡ᴰb = toPathP⁻ q

        goal : (a₀ , b₀) ≡ (a , b)
        goal = ΣPathP (a₀≡a , b₀≡ᴰb)

      on-yes : (Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀)
      on-yes = inr (subst⁻ B a₀≡a b , b₀≢subst-b)
    Σ-remove-inv' a (no a₀≢a) b _ = inl ((a , a₀≢a) , b)

  Σ-remove-inv : (Σ A B ∖ (a₀ , b₀)) → (Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀)
  Σ-remove-inv ((a , b) , neq) = Σ-remove-inv' a (a₀≟ a) b neq

  Σ-remove-rinv : ∀ a → (a₀≟a : Dec (a₀ ≡ a)) → (b : B a) → (neq : (a₀ , b₀) ≢ (a , b))
    → Σ-remove a₀ b₀ is-prop-a₀-loop (Σ-remove-inv' a a₀≟a b neq) ≡ ((a , b) , neq)
  Σ-remove-rinv a (yes a₀≡a) b neq = Remove≡ goal where
    goal : (a₀ , subst⁻ B a₀≡a b) ≡ (a , b)
    goal = ΣPathP (a₀≡a , symP (subst⁻-filler B a₀≡a b))
  Σ-remove-rinv a (no a₀≢a) b neq = Remove≡ $ refl′ (a , b)

  Σ-remove-linv-left : ∀ a → (a₀≟a : Dec (a₀ ≡ a)) → (a₀≢a : a₀ ≢ a) → (b : B a)
    → (let x = inl ((a , a₀≢a) , b))
    → Σ-remove-inv' a a₀≟a b (Σ-remove' x .snd) ≡ x
  Σ-remove-linv-left a (yes a₀≡a) a₀≢a = ex-falso $ a₀≢a a₀≡a
  Σ-remove-linv-left a (no _) _ b = cong inl (ΣPathP (Remove≡ (refl′ a) , refl′ b))

  Σ-remove-linv-right : (a₀≟a₀ : Dec (a₀ ≡ a₀)) → (b : B a₀) → (b₀≢b : b₀ ≢ b)
    → (let x = inr (b , b₀≢b))
    → Σ-remove-inv' a₀ a₀≟a₀ b (Σ-remove' x .snd) ≡ x
  Σ-remove-linv-right (yes a₀≡a₀) b _ = cong inr $ Remove≡ goal where
    goal : subst⁻ B a₀≡a₀ b ≡ b
    goal = cong (λ p → subst⁻ B p b) (is-prop-a₀-loop a₀≡a₀ refl) ∙ substRefl {B = B} b
  Σ-remove-linv-right (no a₀≢a₀) = ex-falso $ a₀≢a₀ refl

  Σ-remove-Iso : Iso ((Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀)) (Σ A B ∖ (a₀ , b₀))
  Σ-remove-Iso .Iso.fun = Σ-remove'
  Σ-remove-Iso .Iso.inv = Σ-remove-inv
  Σ-remove-Iso .Iso.rightInv ((a , b) , neq) = Σ-remove-rinv a (a₀≟ a) b neq
  Σ-remove-Iso .Iso.leftInv (inl ((a , a₀≢a) , b)) = Σ-remove-linv-left a (a₀≟ a) a₀≢a b
  Σ-remove-Iso .Iso.leftInv (inr (b , b₀≢b)) = Σ-remove-linv-right (a₀≟ a₀) b b₀≢b

  isIsolatedFst→Σ-remove-equiv : ((Σ[ (a , _) ∈ A ∖ a₀ ] B a) ⊎ (B a₀ ∖ b₀)) ≃ (Σ A B ∖ (a₀ , b₀))
  isIsolatedFst→Σ-remove-equiv = isoToEquiv Σ-remove-Iso

  isIsolatedFst→isEquiv-Σ-remove : isEquiv (Σ-remove {B = B} a₀ b₀ is-prop-a₀-loop)
  isIsolatedFst→isEquiv-Σ-remove = equivIsEquiv isIsolatedFst→Σ-remove-equiv

isPerfect : (A : Type ℓ) → Type ℓ
isPerfect A = ¬ (A °)

isIsolated→isContrConnectedComponent : {a : A} → isIsolated a → isContr (Σ[ a′ ∈ A ] ∥ a ≡ a′ ∥₁)
isIsolated→isContrConnectedComponent {A} {a} a≟_ = isOfHLevelRespectEquiv 0 singl-equiv (isContrSingl a) where
  singl-equiv : singl a ≃ (Σ[ a′ ∈ A ] ∥ a ≡ a′ ∥₁)
  singl-equiv = Σ-cong-equiv-snd λ a′ → invEquiv (PT.propTruncIdempotent≃ (isIsolated→isPropPath a a≟_ a′))

{-

module Compact where
  isComplemented : {A : Type ℓ} → (B : A → Type ℓ) → Type ℓ
  isComplemented B = ∀ a → Dec (B a)

  isCompact : (A : Type ℓ) → Type _
  isCompact {ℓ} A = ∀ (B : A → Type ℓ) → isComplemented B → Dec (Σ A B)

{-
  isEquiv-Σ-isolate→isCompact : (A : Type ℓ) → (B : A → Type ℓ)
    → isEquiv (Σ-isolate A B)
    → ∀ a → isCompact (B a)
  isEquiv-Σ-isolate→isCompact A B is-equiv-Σ-isolate a P is-complemented-P = {! !}

  isCompact→isEquiv-Σ-isolate : (A : Type ℓ) → (B : A → Type ℓ)
    → (∀ a → isCompact (B a))
    → isEquiv (Σ-isolate A B)
  isCompact→isEquiv-Σ-isolate A B is-compact-B = isIsolatedPair→isEquiv-Σ-isolated is-isolated-pair where
    is-isolated-pair : {a₀ : A} {b₀ : B a₀} → isIsolated (a₀ , b₀) → isIsolated a₀ × isIsolated b₀
    is-isolated-pair {a₀} {b₀} isolated-ab = {! !}
-}

module Comodality where
  _⇀_ : (A B : Type ℓ) → Type ℓ
  A ⇀ B = Σ[ f ∈ (A → B) ] ∀ {a} → isIsolated a → isIsolated (f a)

  infix 1 _⇀_

  Equiv→⇀ : (e : A ≃ B) → (A ⇀ B)
  Equiv→⇀ e .fst = equivFun e
  Equiv→⇀ e .snd = isIsolatedPreserveEquiv e _

  ⇀-≡ : {f g : A ⇀ B} → f .fst ≡ g .fst → f ≡ g
  ⇀-≡ = Σ≡Prop λ f → isPropImplicitΠ λ a → isProp→ (isPropIsIsolated (f a))

  _⋄_ : ∀ {A B C : Type ℓ} → (f : A ⇀ B) (g : B ⇀ C) → (A ⇀ C)
  ((f , f-create-isolated) ⋄ (g , g-create-isolated)) .fst = f ⨟ g
  ((f , f-create-isolated) ⋄ (g , g-create-isolated)) .snd = g-create-isolated ∘ f-create-isolated

  infixr 10 _⋄_

  id° : (A : Type ℓ) → A ⇀ A
  id° A .fst = λ a → a
  id° A .snd = λ iso → iso

  [_]° : (f : A ⇀ B) → A ° ⇀ B °
  [ f , f-create-isolated ]° .fst (a , isolated-a) = (f a , f-create-isolated isolated-a)
  [ f , f-create-isolated ]° .snd {a = a₀ , isolated-a₀} _ = isIsolatedΣSndProp
    (f-create-isolated isolated-a₀)
    (isPropIsIsolated (f a₀))

  dig-equiv : A ° ≃ (A °) °
  dig-equiv = invEquiv (Discrete→IsolatedEquiv DiscreteIsolated)

  dig : A ° ⇀ (A °) °
  dig = Equiv→⇀ dig-equiv

  derelict : A ° ⇀ A
  derelict .fst = forget-isolated
  derelict .snd {a = a₀ , is-isolated-a₀} _ = is-isolated-a₀

  counit-left : (dig ⋄ [ derelict ]°) ≡ id° (A °)
  counit-left = ⇀-≡ refl

  counit-right : (dig ⋄ derelict {A = A °}) ≡ id° (A °)
  counit-right = ⇀-≡ refl

  comul : dig {A = A} ⋄ dig {A = A °} ≡ dig ⋄ [ dig {A = A} ]°
  comul = ⇀-≡ $ funExt λ { a° → Isolated≡ $ Isolated≡ $ refl′ a° }

  contract : A ° ⇀ A ° × A °
  contract .fst a = a , a
  contract .snd iso-a = isIsolatedΣ iso-a iso-a

{-
  [_×_] : ∀ {A₀ A₁ B₀ B₁ : Type ℓ}
    → (f₀ : A₀ ° ⇀ B₀ °)
    → (f₁ : A₁ ° ⇀ B₁ °)
    → A₀ ° × A₁ ° ⇀ B₀ ° × B₁ °
  [ f × g ] .fst = Σ-map (f .fst) λ _ → (g .fst)
  [ f × g ] .snd {a = a₀ , a₁} = {! !}

  weaken : A ° → ⊤ ℓ
  weaken = const _

  dig-comonoid-hom : dig ⋄ contract ≡ contract {A = A} ⋄ [ dig × dig ]
  dig-comonoid-hom = ⇀-≡ refl

  par : A ° × A ⇀ A °
  par .fst (a° , a) = {! !}
  par .snd = {! !}
-}
-}
