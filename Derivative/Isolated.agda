{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Derivative.Isolated where

open import Derivative.Prelude
open import Derivative.Decidable
  as Dec
  using
    ( locallyDiscrete→locallyIsPropPath
    ; Dec ; yes ; no
    ; Discrete
    ; isProp¬
    )
open import Derivative.Remove
open import Derivative.Sum as Sum using (_⊎_ ; inl ; inr)
open import Derivative.W as W

open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv ; hasRetract ; hasSection ; congEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (toPathP⁻)
open import Cubical.Foundations.Transport using (subst⁻ ; subst⁻-filler)
open import Cubical.Functions.Embedding
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
  isSetIsolated = Dec.Discrete→isSet DiscreteIsolated

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
  EmbeddingReflectIsolated : (f : A → B) → isEmbedding f → ∀ {a} → isIsolated (f a) → isIsolated a
  EmbeddingReflectIsolated f emb-f {a} isolated-fa a′ =
    Dec.map
      (isEmbedding→Inj emb-f a a′)
      (λ fa≢fa′ a≡a′ → fa≢fa′ $ cong f a≡a′)
      (isolated-fa (f a′))

isIsolatedFromInl : ∀ {a : A} → isIsolated (inl {B = B} a) → isIsolated a
isIsolatedFromInl = EmbeddingReflectIsolated inl Sum.isEmbedding-inl

isIsolatedFromInr : ∀ {b : B} → isIsolated (inr {A = A} b) → isIsolated b
isIsolatedFromInr = EmbeddingReflectIsolated inr Sum.isEmbedding-inr

isIsolatedInl : ∀ {a : A} → isIsolated a → isIsolated (inl {B = B} a)
isIsolatedInl {a} isolated-a (inl a′) = Dec.decEquiv (cong inl , Sum.isEmbedding-inl a a′) (isolated-a a′)
isIsolatedInl {a} isolated-a (inr b) = no λ inl≡inr → Sum.⊎Path.encode _ _ inl≡inr .lower

isIsolatedInr : ∀ {b : B} → isIsolated b → isIsolated (inr {A = A} b)
isIsolatedInr {b} isolated-b (inl a) = no λ inr≡inl → Sum.⊎Path.encode _ _ inr≡inl .lower
isIsolatedInr {b} isolated-b (inr b′) = Dec.decEquiv (cong inr , Sum.isEmbedding-inr b b′) (isolated-b b′)

IsolatedSumIso : Iso ((A ⊎ B) °) ((A °) ⊎ (B °))
IsolatedSumIso .Iso.fun (inl a , isolated-inl-a) = inl (a , isIsolatedFromInl isolated-inl-a)
IsolatedSumIso .Iso.fun (inr b , isolated-inr-b) = inr (b , isIsolatedFromInr isolated-inr-b)
IsolatedSumIso .Iso.inv (inl (a , isolated-a)) = inl a , isIsolatedInl isolated-a
IsolatedSumIso .Iso.inv (inr (b , isolated-b)) = inr b , isIsolatedInr isolated-b
IsolatedSumIso .Iso.rightInv (inl (a , _)) = cong inl $ Isolated≡ $ refl′ a
IsolatedSumIso .Iso.rightInv (inr (b , _)) = cong inr $ Isolated≡ $ refl′ b
IsolatedSumIso .Iso.leftInv (inl a , _) = Isolated≡ $ refl′ $ inl a
IsolatedSumIso .Iso.leftInv (inr b , _) = Isolated≡ $ refl′ $ inr b

IsolatedSumEquiv : (A ⊎ B) ° ≃ (A °) ⊎ (B °)
IsolatedSumEquiv = isoToEquiv IsolatedSumIso

opaque
  isIsolatedTransport : (a : A) (p : A ≡ B) → isIsolated a → isIsolated (transport p a)
  isIsolatedTransport a = J (λ B p → isIsolated a → isIsolated (transport p a)) λ where
    isolated-a a′ → subst (λ - → Dec (- ≡ a′)) (sym $ transportRefl a) (isolated-a a′)

  isIsolatedSubst : (B : A → Type ℓ) {x y : A} (p : x ≡ y)
    → {b : B x}
    → isIsolated b
    → isIsolated (subst B p b)
  isIsolatedSubst B p {b} = isIsolatedTransport b (cong B p)

isProp→isIsolated : isProp A → (a : A) → isIsolated a
isProp→isIsolated prop-A a b = yes $ prop-A a b

isProp→IsolatedEquiv : ∀ {P : Type ℓ} → isProp P → (P °) ≃ P
isProp→IsolatedEquiv = Discrete→IsolatedEquiv ∘ Dec.isProp→Discrete

isContr→isIsolatedCenter : isContr A → (a : A) → isIsolated a
isContr→isIsolatedCenter = isProp→isIsolated ∘ isContr→isProp

remove-emb : (a : A) → A ∖ a → A
remove-emb a = fst

module _ {ℓS ℓP ℓQ} {S : Type ℓS} {P : S → Type ℓP} {Q : S → Type ℓQ} where
  private
    variable
      s : S
      f : P s → W S P

  isIsolatedTop : ∀ {q : Q s} → isIsolated q → isIsolated {A = Wᴰ S P Q (sup s f)} (top q)
  isIsolatedTop {s} {f} {q} isolated-q (top q′) = {! EmbeddingReflectIsolated !}
  isIsolatedTop {s} {f} {q} isolated-q (below p b) = {! !}

  isIsolatedFromTop : ∀ {q : Q s} → isIsolated {A = Wᴰ S P Q (sup s f)} (top q) → isIsolated q
  isIsolatedFromTop {s} {f} {q} isolated-top = isIsolatedFromInl isolated-inl where
    isolated-inl : isIsolated {A = Q s ⊎ (Σ[ p ∈ P s ] (Wᴰ S P Q (f p)))} (inl q)
    isolated-inl = isIsolatedPreserveEquiv (Wᴰ-out-equiv _ _ _ s f) (top q) isolated-top

  isIsolatedBelow : ∀ {p : P s} {wᴰ : Wᴰ S P Q (f p)}
    → isIsolated {A = Σ[ p ∈ P s ] Wᴰ S P Q (f p)} (p , wᴰ)
    → isIsolated {A = Wᴰ S P Q (sup s f)} (below p wᴰ)
  isIsolatedBelow = {! !}

  isIsolatedFromBelow : ∀ {p : P s} {wᴰ : Wᴰ S P Q (f p)}
    → isIsolated {A = Wᴰ S P Q (sup s f)} (below p wᴰ)
    → isIsolated {A = Σ[ p ∈ P s ] Wᴰ S P Q (f p)} (p , wᴰ)
  isIsolatedFromBelow {s} {f} {p} {wᴰ} isolated-below = isIsolatedFromInr isolated-inr where
    isolated-inr : isIsolated {A = Q s ⊎ (Σ[ p ∈ P s ] (Wᴰ S P Q (f p)))} (inr (p , wᴰ))
    isolated-inr = isIsolatedPreserveEquiv (Wᴰ-out-equiv _ _ _ s f) (below p wᴰ) isolated-below

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
Σ-isolate A B ((a , isolated-a) , b , isolated-b) .fst = a , b
Σ-isolate A B ((a , isolated-a) , b , isolated-b) .snd = isIsolatedΣ isolated-a isolated-b

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

module _ {A : Type ℓ} {B : A → Type ℓ} (is-equiv-Σ-isolate : isEquiv (Σ-isolate A B)) where
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

isEquiv-Σ-isolate≃isIsolatedPair : (A : Type ℓ) (B : A → Type ℓ)
 → isEquiv (Σ-isolate A B) ≃ (∀ {a₀ : A} {b₀ : B a₀} → isIsolated {A = Σ A B} (a₀ , b₀) → isIsolated a₀ × isIsolated b₀)
isEquiv-Σ-isolate≃isIsolatedPair A B = propBiimpl→Equiv
  (isPropIsEquiv _)
  (isPropImplicitΠ2 λ a₀ b₀ → isProp→ (isProp× (isPropIsIsolated a₀) (isPropIsIsolated b₀)))
  isEquiv-Σ-isolate→isIsolatedPair
  isIsolatedPair→isEquiv-Σ-isolated

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

stitch : (a° : A °) → (((A ∖ a° .fst) → B) × B) → (A → B)
stitch a° (f , b₀) = elimIsolated a° (λ _ _ → b₀) f

stitch' : (a° : A °) → (((A ∖ a° .fst) → B) × B) → (A → B)
stitch' (a₀ , a₀≟_) (f , b₀) a with a₀≟ a
... | (yes p) = b₀
... | (no ¬p) = f (a , ¬p)

stitch-β : (a° : A °) (f : (A ∖ a° .fst) → B) {b₀ : B} → stitch a° (f , b₀) (a° .fst) ≡ b₀
stitch-β a° f {b₀} = elimIsolated-β-refl a° (λ _ _ → b₀) f

stitch-β' : (a° : A °) (f : (A ∖ a° .fst) → B) {b₀ : B} (a : A ∖ a° .fst) → stitch a° (f , b₀) (a .fst) ≡ f a
stitch-β' a° f {b₀} = uncurry $ elimIsolated-β-no a° (λ _ _ → b₀) f

stitch'-β : (a° : A °) (f : (A ∖ a° .fst) → B) {b₀ : B} → stitch' a° (f , b₀) (a° .fst) ≡ b₀
stitch'-β (a₀ , a₀≟_) f {b₀} with (a₀≟ a₀)
... | (yes p) = refl
... | (no ¬p) = ex-falso $ ¬p refl

unstitch : (a° : A °) → (A → B) → (((A ∖ a° .fst) → B) × B)
unstitch (a₀ , _) f .fst = f ∘ fst
unstitch (a₀ , _) f .snd = f a₀

isEquivStitch' : (a° : A °) → isEquiv (stitch' {B = B} a°)
isEquivStitch' {A} {B} a°@(a₀ , a₀≟_) = isoToIsEquiv stich-iso module isEquivStitch' where

  stich-iso : Iso (((A ∖ a₀) → B) × B) (A → B)
  stich-iso .Iso.fun = stitch' a°
  stich-iso .Iso.inv = unstitch a°
  stich-iso .Iso.rightInv f = funExt rinv where
    rinv : ∀ a → stitch' a° (unstitch a° f) a ≡ f a
    rinv a with a₀≟ a
    ... | (yes p) = cong f p
    ... | (no ¬p) = refl
  stich-iso .Iso.leftInv (f° , b) = linv where
    linv-fst : ∀ a → unstitch a° (stitch' a° (f° , b)) .fst a ≡ f° a
    linv-fst (a , a₀≢a) with (a₀≟ a)
    ... | (yes a₀≡a) = ex-falso (a₀≢a a₀≡a)
    ... | (no a₀≢a') = cong (λ - → f° (a , -)) (isProp¬ _ a₀≢a' a₀≢a)

    linv-snd : stitch' a° (f° , b) a₀ ≡ b
    linv-snd with (a₀≟ a₀)
    ... | (yes _) = refl
    ... | (no a₀≢a₀) = ex-falso (a₀≢a₀ refl)

    linv : unstitch a° (stitch' a° (f° , b)) ≡ (f° , b)
    linv = ΣPathP (funExt linv-fst , linv-snd)

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
stitchEquiv a° .fst = stitch' a°
stitchEquiv a° .snd = isEquivStitch' a°

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
