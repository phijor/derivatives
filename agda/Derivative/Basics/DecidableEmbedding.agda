{-# OPTIONS --safe #-}
module Derivative.Basics.DecidableEmbedding where

open import Derivative.Prelude
open import Derivative.Basics.Decidable as Dec
open import Derivative.Basics.Embedding
open import Derivative.Basics.Equiv using (postCompEquivFiberEquiv ; symEquiv)
open import Derivative.Basics.Function
open import Derivative.Basics.Sigma
open import Derivative.Basics.Sum as Sum
open import Derivative.Basics.Unit
open import Derivative.Isolated.Base

open import Cubical.Foundations.Equiv.Properties using (preCompEquiv ; equivAdjointEquiv)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Bool as Bool
open import Cubical.Data.Sigma.Properties
open import Cubical.Functions.Embedding


private
  variable
    ℓ ℓX ℓA : Level
    A B C X : Type ℓ

isDecEmbedding : (f : X → A) → Type _
isDecEmbedding {X} {A} f = ∀ a → Dec (fiber f a) × isProp (fiber f a)

private
  isPropFiber→isPropFiberLEM : (f : X → A)
    → ∀ a → isProp (fiber f a) → isProp ((¬ fiber f a) ⊎ fiber f a)
  isPropFiber→isPropFiberLEM f a prop-fiber = Sum.isProp⊎ (isProp¬ _) prop-fiber _$_

  isDecFiber→inhFiberLEM : (f : X → A) → ∀ a → Dec (fiber f a) → ((¬ fiber f a) ⊎ fiber f a)
  isDecFiber→inhFiberLEM f a (yes fib) = inr fib
  isDecFiber→inhFiberLEM f a (no ¬fib) = inl ¬fib

isDecEmbedding→fiberLEM : (f : X → A) → isDecEmbedding f
  → ∀ a → isContr ((¬ fiber f a) ⊎ fiber f a)
isDecEmbedding→fiberLEM f dec-emb-f a =
  inhProp→isContr
    (isDecFiber→inhFiberLEM f a $ dec-emb-f a .fst)
    (isPropFiber→isPropFiberLEM f a $ dec-emb-f a .snd)

_↪°_ : ∀ {ℓX ℓA} (X : Type ℓX) → (A : Type ℓA) → Type _
X ↪° A = Σ[ f ∈ (X → A) ] isDecEmbedding f

module Notation (ι : X ↪° A) where
  fun : X → A
  fun = ι .fst

  has-prop-fibers : ∀ a → isProp (fiber fun a)
  has-prop-fibers a = ι .snd a .snd

  has-dec-fibers : ∀ a → Dec (fiber fun a)
  has-dec-fibers a = ι .snd a .fst

  cancel : ∀ {x y : X} → fun x ≡ fun y → x ≡ y
  cancel {x} {y} p = cong fst fib-path where
    fib₁ : fiber fun (fun y)
    fib₁ .fst = x
    fib₁ .snd = p

    fib₂ : fiber fun (fun y)
    fib₂ .fst = y
    fib₂ .snd = refl

    fib-path : fib₁ ≡ fib₂
    fib-path = has-prop-fibers (fun y) _ _


DecEmbedding : (ℓX : Level) → (A : Type ℓA) → Type (ℓ-max (ℓ-suc ℓX) ℓA)
DecEmbedding ℓX A = Σ[ X ∈ Type ℓX ] (X ↪° A)

test : A ° ≃ (𝟙 ↪° A)
test {A = A} =
  Σ[ a ∈ A ] (∀ b → Dec (a ≡ b))
    ≃⟨ Σ-cong-equiv-snd (λ a → invEquiv $ Σ-contractSnd λ locally-dec → isContrΠ λ b → inhProp→isContr (locallyDiscrete→locallyIsPropPath a locally-dec b) isPropIsProp) ⟩
  Σ[ a ∈ A ] (∀ b → Dec (a ≡ b)) × (∀ b → isProp (a ≡ b))
    ≃⟨ Σ-cong-equiv-snd (λ a → invEquiv Σ-Π-≃) ⟩
  Σ[ a ∈ A ] ((b : A) → Dec (a ≡ b) × isProp (a ≡ b))
    ≃⟨ Σ-cong-equiv-snd (equivΠCod ∘ shuffle) ⟩
  Σ[ a ∈ A ] ((b : A) → Dec (𝟙* × (a ≡ b)) × isProp (𝟙* × (a ≡ b)))
    ≃⟨ Σ-cong-equiv-fst $ invEquiv $ Π𝟙*-equiv (λ _ → A) ⟩
  (Σ[ f ∈ (𝟙 → A) ] ∀ a → Dec (fiber f a) × isProp (fiber f a))
    ≃∎
    where
      open import Cubical.Foundations.Transport using (substEquiv)
      open import Cubical.Foundations.Univalence using (ua)

      shuffle : (a b : A) → (Dec (a ≡ b) × isProp (a ≡ b)) ≃ (Dec (𝟙* × (a ≡ b)) × isProp (𝟙* × (a ≡ b)))
      shuffle a b = substEquiv (λ - → Dec - × isProp -) $ ua $ invEquiv 𝟙*-unit-×-left-equiv

module _ (f : X → A) (dec-emb : isDecEmbedding f) (a : A) where
  isDecEmbedding→isPropDecFiber : isProp (Dec (fiber f a))
  isDecEmbedding→isPropDecFiber = Dec.isPropDec (dec-emb a .snd)

isPropIsDecEmbedding : (f : X → A) → isProp (isDecEmbedding f)
isPropIsDecEmbedding f = isPropFromPointed→isProp λ where
  dec-emb → isPropΠ λ where
    a → isProp×
      (isDecEmbedding→isPropDecFiber f dec-emb a)
      isPropIsProp

↪°-≡-equiv : {f g : X ↪° A} → (f .fst ≡ g .fst) ≃ (f ≡ g)
↪°-≡-equiv = Σ≡PropEquiv isPropIsDecEmbedding

↪°-≡ : {f g : X ↪° A} → f .fst ≡ g .fst → f ≡ g
↪°-≡ = equivFun ↪°-≡-equiv

comp-dec-emb : (f : A ↪° B) (g : B ↪° C) → A ↪° C
comp-dec-emb (f , dec-emb-f) (g , dec-emb-g) .fst = f ⨟ g
comp-dec-emb (f , dec-emb-f) (g , dec-emb-g) .snd c = dec-fiber , prop-fiber where
  dec-fiber : Dec (fiber (f ⨟ g) c)
  dec-fiber = decEquiv (invEquiv (⨟-fiber-equiv f g c)) $
    decΣProp (dec-emb-g c .snd) (dec-emb-g c .fst) λ where
      (b , gb≡c) → dec-emb-f b .fst

  prop-fiber : isProp (fiber (f ⨟ g) c)
  prop-fiber = isOfHLevelRespectEquiv 1 (invEquiv (⨟-fiber-equiv f g c)) $
    isPropΣ (dec-emb-g c .snd) λ where
      (b , gb≡c) → dec-emb-f b .snd

isDecEmbedding-𝟘 : (f : 𝟘 → A) → isDecEmbedding f
isDecEmbedding-𝟘 f a .fst = no λ ()
isDecEmbedding-𝟘 f a .snd = λ ()

isContrDecEmbedding-𝟘 : isContr (𝟘 ↪° A)
isContrDecEmbedding-𝟘 = inhProp→isContr
  ((λ ()) , isDecEmbedding-𝟘 _)
  (isPropΣ (λ f g → funExt λ ()) isPropIsDecEmbedding)

is-dec-emb-inl : isDecEmbedding (inl {A = A} {B = B})
is-dec-emb-inl y = dec-fiber y , hasPropFibersInl y where
  dec-fiber : ∀ y → Dec (fiber inl y)
  dec-fiber (inl a) = yes (a , refl)
  dec-fiber (inr b) = no $ inr≢inl ∘ sym ∘ snd

inl-dec-emb : A ↪° (A ⊎ B)
inl-dec-emb .fst = inl
inl-dec-emb .snd = is-dec-emb-inl

is-dec-emb-inr : isDecEmbedding (inr {A = A} {B = B})
is-dec-emb-inr y = dec-fiber y , hasPropFibersInr y where
  dec-fiber : ∀ y → Dec (fiber inr y)
  dec-fiber (inl a) = no $ inr≢inl ∘ snd
  dec-fiber (inr b) = yes (b , refl)

inr-dec-emb : B ↪° (A ⊎ B)
inr-dec-emb .fst = inr
inr-dec-emb .snd = is-dec-emb-inr

embed-sum : ((A ⊎ B) ↪° C) → Σ[ α ∈ A ↪° C ] Σ[ β ∈ B ↪° C ] ∀ c → ¬ fiber (α .fst) c × fiber (β .fst) c
embed-sum {A} {B} {C} ι = α , β , not-fiber where
  module ι = Notation ι
  α : A ↪° C
  α = comp-dec-emb inl-dec-emb ι

  β : B ↪° C
  β = comp-dec-emb inr-dec-emb ι

  not-fiber : ∀ c → ¬ fiber (α .fst) c × fiber (β .fst) c
  not-fiber c ((a , ιinla≡c) , (b , ιinrb≡c)) = inl≢inr (ι.cancel (ιinla≡c ∙ sym ιinrb≡c))

Complement : (B : Type ℓ) → (f : A → B) → Type _
Complement B f = Σ[ b ∈ B ] ¬ fiber f b

Complement≡ : {f : A → B} → {x y : Complement B f} → x .fst ≡ y .fst → x ≡ y
Complement≡ {f} = Σ≡Prop λ b → isProp¬ (fiber f b)

_-_ : (B : Type ℓ) → (f : A → B) → Type _
_-_ = Complement

complementSubstEquiv' : (f : A → B) (e : C ≃ B) → (C - (f ⨟ invEq e)) ≃ (B - f)
complementSubstEquiv' f e = Σ-map-equiv e ¬fiber-equiv where
  ¬fiber-equiv : ∀ c → (¬ fiber (f ⨟ invEq e) c) ≃ (¬ fiber f (equivFun e c))
  ¬fiber-equiv c = preCompEquiv $ Σ-cong-equiv-snd λ a → symEquiv ∙ₑ invEquiv (equivAdjointEquiv e) ∙ₑ symEquiv

complementSubstEquiv : (f : A → B) (e : B ≃ C) → (C - (f ⨟ equivFun e)) ≃ (B - f)
complementSubstEquiv f e = Σ-map-equiv (invEquiv e) ¬fiber-equiv where
  ¬fiber-equiv : ∀ c → (¬ fiber (f ⨟ equivFun e) c) ≃ (¬ fiber f (equivFun (invEquiv e) c))
  ¬fiber-equiv c = preCompEquiv $ invEquiv $ postCompEquivFiberEquiv f e c

sum-inr-remove : A → (A ⊎ B) - inr
sum-inr-remove a .fst = inl a
sum-inr-remove a .snd = uncurry λ _ → inr≢inl

sum-inr-remove-fiber-equiv : (y : (A ⊎ B) - inr) → fiber inl (y .fst) ≃ fiber sum-inr-remove y
sum-inr-remove-fiber-equiv {A} y =
  Σ[ a ∈ A ] inl a ≡ y .fst
    ≃⟨ Σ-cong-equiv-snd (λ a → (Σ≡PropEquiv λ _ → isProp¬ _)) ⟩
  Σ[ a ∈ A ] sum-inr-remove a ≡ y
    ≃∎

isEquiv-sum-inr-remove : isEquiv (sum-inr-remove {A = A} {B = B})
isEquiv-sum-inr-remove .equiv-proof y = inhProp→isContr (inh-fiber y) (prop-fiber y) where
  inh-fiber : (y : (A ⊎ B) - inr) → fiber sum-inr-remove y
  inh-fiber (inl a , _) .fst = a
  inh-fiber (inl a , _) .snd = Complement≡ $ refl′ (inl a)
  inh-fiber (inr b , hb) = ex-falso $ hb (b , refl′ (inr b))

  prop-fiber : (y : (A ⊎ B) - inr) → isProp (fiber sum-inr-remove y)
  prop-fiber y = isOfHLevelRespectEquiv 1 (sum-inr-remove-fiber-equiv y) (hasPropFibersInl (y .fst))

sum-inr-remove-equiv : A ≃ (A ⊎ B) - inr
sum-inr-remove-equiv .fst = sum-inr-remove
sum-inr-remove-equiv .snd = isEquiv-sum-inr-remove

remove-sum-left : (f : A → B) → (B - f) ⊎ A → B
remove-sum-left f (inl b) = b .fst
remove-sum-left f (inr a) = f a

remove-sum-left-fiber-equiv :
  ∀ (f : A → B)
  → (hasPropFibers f)
  → (b : B)
  → fiber (remove-sum-left f) b ≃ ((¬ fiber f b) ⊎ (fiber f b))
remove-sum-left-fiber-equiv {A} {B} f f-emb b =
  Σ[ x ∈ (B - f) ⊎ A ] remove-sum-left f x ≡ b
    ≃⟨ Σ-⊎-fst-≃ ⟩
  (Σ[ x ∈ (B - f) ] x .fst ≡ b) ⊎ (fiber f b)
    ≃⟨ ⊎-left-≃ shuffle ⟩
  (¬ fiber f b) ⊎ (fiber f b)
    ≃∎
    where
     shuffle : (Σ[ x ∈ (B - f) ] x .fst ≡ b) ≃ (¬ fiber f b)
     shuffle =
      Σ[ x ∈ (B - f) ] x .fst ≡ b
        ≃⟨ Σ-assoc-≃ ⟩
      Σ[ b′ ∈ B ] (¬ fiber f b′) × (b′ ≡ b)
        ≃⟨ strictEquiv
          (λ (b′ , fib , p) → ((b′ , sym p) , fib))
          (λ ((b′ , p) , fib) → (b′ , fib , sym p))
        ⟩
      Σ[ (b′ , _) ∈ singl b ] (¬ fiber f b′)
        ≃⟨ Σ-contractFst (isContrSingl b) ⟩
      ¬ fiber f b
        ≃∎

isDecEmbedding→isEquiv-remove-sum-left : (f : A → B) → isDecEmbedding f → isEquiv (remove-sum-left f)
isDecEmbedding→isEquiv-remove-sum-left f dec-emb-f .equiv-proof b =
  isOfHLevelRespectEquiv 0
    (invEquiv (remove-sum-left-fiber-equiv f (snd ∘ dec-emb-f) b))
    (isDecEmbedding→fiberLEM f dec-emb-f b)

remove-sum-left-Iso : (f : A ↪° B) → Iso ((B - (f .fst)) ⊎ A) B
remove-sum-left-Iso {A} {B} (f , dec-emb-f) = goal module remove-sum-left-Iso where
  inv' : (b : B) → Dec (fiber f b) → (B - f) ⊎ A
  inv' b (yes (a , _)) = inr a
  inv' b (no ¬fib) = inl (b , ¬fib)

  inv : B → (B - f) ⊎ A
  inv b = inv' b (dec-emb-f b .fst)

  sec' : ∀ b → (b∈? : Dec (fiber f b)) → remove-sum-left f (inv' b b∈?) ≡ b
  sec' b (yes (a , fa≡b)) = fa≡b
  sec' b (no _) = refl′ b

  sec : ∀ b → remove-sum-left f (inv b) ≡ b
  sec b = sec' b $ dec-emb-f b .fst

  ret' : (x : (B - f) ⊎ A)
    → (h : Dec (fiber f (remove-sum-left f x)))
    → inv' (remove-sum-left f x) h ≡ x
  ret' (inl (b , ¬fib)) (yes fib) = ex-falso (¬fib fib)
  ret' (inl (b , _)) (no _) = cong inl $ Complement≡ (refl′ b)
  ret' (inr a) (yes fib) = cong (inr ∘ fst) fiber-path where
    --- f is an embedding (= has propositional fibers)
    fiber-path : Path (fiber f (f a)) fib (a , refl)
    fiber-path = dec-emb-f (f a) .snd _ _
  ret' (inr a) (no ¬fib) = ex-falso (¬fib (a , refl))

  ret : ∀ x → inv (remove-sum-left f x) ≡ x
  ret x = ret' x $ dec-emb-f (remove-sum-left f x) .fst


  goal : Iso _ _
  goal .Iso.fun = remove-sum-left f
  goal .Iso.inv = inv
  goal .Iso.rightInv = sec
  goal .Iso.leftInv = ret
  {-# INLINE goal #-}

remove-sum-left-equiv : (f : A ↪° B) → (B - (f .fst)) ⊎ A ≃ B
remove-sum-left-equiv = isoToEquiv ∘ remove-sum-left-Iso

remove-sum-left-equiv' : (f : A ↪° B) → (B - (f .fst)) ⊎ A ≃ B
remove-sum-left-equiv' (f , dec-emb-f) .fst = remove-sum-left f
remove-sum-left-equiv' (f , dec-emb-f) .snd = isDecEmbedding→isEquiv-remove-sum-left f dec-emb-f

dec-emb-postcomp-equiv : (f : X ↪° A) → (e : A ≃ B) → (X ↪° B)
dec-emb-postcomp-equiv (f , dec-emb-f) e .fst = f ⨟ equivFun e
dec-emb-postcomp-equiv (f , dec-emb-f) e .snd b = goal where
  fiber-equiv : fiber f (invEq e b) ≃ fiber (f ⨟ equivFun e) b
  fiber-equiv = invEquiv $ postCompEquivFiberEquiv f e b

  goal : Dec (fiber (f ⨟ equivFun e) b) × isProp (fiber (f ⨟ equivFun e) b)
  goal .fst = decEquiv fiber-equiv $ dec-emb-f (invEq e b) .fst
  goal .snd = isOfHLevelRespectEquiv 1 fiber-equiv $ dec-emb-f (invEq e b) .snd

module Examples where
  open import Cubical.Data.Nat

  private
    empty-fib : (f : X → A) → ∀ a → ¬ fiber f a → Dec (fiber f a) × isProp (fiber f a)
    empty-fib f a ¬fib .fst = no ¬fib
    empty-fib f a ¬fib .snd fib₁ fib₂ = ex-falso $ ¬fib fib₁

  --- Non-trivial decidable self-embedding:
  suc-emb : ℕ ↪° ℕ
  suc-emb .fst = suc
  suc-emb .snd zero = empty-fib suc zero $ uncurry λ _ → snotz
  suc-emb .snd (suc n) .fst = yes (n , refl)
  suc-emb .snd (suc n) .snd (k , suc-k≡n) (l , suc-l≡n) = Σ≡Prop (λ _ → isSetℕ _ _) $ injSuc $ suc-k≡n ∙ sym suc-l≡n
