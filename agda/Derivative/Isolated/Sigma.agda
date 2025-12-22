{-# OPTIONS --safe #-}
module Derivative.Isolated.Sigma where

open import Derivative.Prelude
open import Derivative.Basics.Decidable as Dec
open import Derivative.Basics.Embedding

open import Derivative.Isolated.Base

open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv)
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

private
  variable
    ℓ : Level
    A : Type ℓ
    B : A → Type ℓ

isIsolatedΣ : ∀ {a : A} {b : B a}
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

_,°_ : (a : A °) → (b : B (a .fst) °) → (Σ[ a ∈ A ] B a) °
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

module _ (is-equiv-Σ-isolate : isEquiv (Σ-isolate A B)) where
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

isIsolatedPair→isEquiv-Σ-isolated :
  (∀ {a₀ : A} {b₀ : B a₀} → isIsolated {A = Σ A B} (a₀ , b₀) → isIsolated a₀ × isIsolated b₀)
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

isIsolated→isEmbeddingInjSnd : (a₀ : A) → isIsolated a₀ → isEmbedding {A = B a₀} {B = Σ A B} (a₀ ,_)
isIsolated→isEmbeddingInjSnd {A} {B} a₀ is-isolated-a₀ = λ b₀ b₁ → equivIsEquiv $ isoToEquiv (path-iso b₀ b₁) where
  path-iso : (b₀ b₁ : B a₀) → Iso (b₀ ≡ b₁) ((a₀ , b₀) ≡ (a₀ , b₁))
  path-iso b₀ b₁ =
    (b₀ ≡ b₁)
      Iso⟨ invIso (Σ-contractFstIso (isIsolated→isContrLoop a₀ is-isolated-a₀)) ⟩
    Σ[ p ∈ a₀ ≡ a₀ ] PathP (λ i → B (p i)) b₀ b₁
      Iso⟨ ΣPathPIsoPathPΣ {B = λ i → B} ⟩
    ((a₀ , b₀) ≡ (a₀ , b₁))
      ∎Iso

isIsolatedFst→isIsolatedSnd≃isIsolatedPair : {a₀ : A} → isIsolated a₀ → (b₀ : B a₀) → isIsolated b₀ ≃ isIsolated {A = Σ A B} (a₀ , b₀)
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

Discrete→isEquiv-Σ-isolate : Discrete A → (∀ a → Discrete (B a)) → isEquiv (Σ-isolate A B)
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

