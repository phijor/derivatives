module Derivative.Prelude where

open import Derivative.Square

open import Cubical.Foundations.Prelude hiding (_◁_ ; hcomp ; comp) public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Structure public
open import Cubical.Foundations.Isomorphism hiding (iso) public
open import Cubical.Foundations.Equiv renaming (_■ to _≃∎) public
open import Cubical.Foundations.HLevels public
open import Cubical.Reflection.StrictEquiv public
open import Cubical.Data.Sigma using (_×_ ; ΣPathP ; Σ≡Prop ; ∃-syntax ; ∃!-syntax) public
open import Cubical.Data.Unit.Base using (tt ; tt*) public
open import Cubical.Relation.Nullary.Base using (¬_) public

import      Cubical.Core.Primitives as Primitives
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma hiding (hcomp ; comp)
import      Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Base using (ℕ ; zero ; suc)
open import Cubical.Data.Unit.Base
open import Cubical.Data.Unit.Properties using (isContr→Iso2)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

private
  variable
    ℓ : Level
    A B C : Type ℓ

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

doubleCompPathP : (B : A → Type ℓ)
  → {x y z w : A}
  → {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} {s : x ≡ w}
  → (filler : Square (sym p) r q s)
  → {xᴰ : B x} {yᴰ : B y} {zᴰ : B z} {wᴰ : B w}
  → (pᴰ : PathP (λ i → B (p i)) xᴰ yᴰ)
  → (qᴰ : PathP (λ i → B (q i)) yᴰ zᴰ)
  → (rᴰ : PathP (λ i → B (r i)) zᴰ wᴰ)
  → PathP (λ i → B (s i)) xᴰ wᴰ
doubleCompPathP B filler pᴰ qᴰ rᴰ i =
  compᴵ (λ j → B (filler i j)) (∂ᴵ i)
  λ where
    j (i = i0) → pᴰ (~ j)
    j (i = i1) → rᴰ j
    j (j = i0) → qᴰ i

module _
  {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {l : a₀₀ ≡ a₀₁} {r : a₁₀ ≡ a₁₁}
  {b : a₀₀ ≡ a₁₀} {t : a₀₁ ≡ a₁₁}
  where
  flipSquareH : Square l r b t → Square (sym l) (sym r) t b
  flipSquareH sq i j = sq i (~ j)

-- refl with explicit argument
refl′ : (a : A) → a ≡ a
refl′ a i = a

module _
  {a₀₀ a₀₁ a₁₋ : A}
  {l : a₀₀ ≡ a₀₁}
  {b : a₀₀ ≡ a₁₋} {t : a₀₁ ≡ a₁₋}
  where
  -- mangleSquare : Square l (refl′ a₁₋) b t → Square (sym l) (sym t) (refl′ a₁₋) {! !}
  -- mangleSquare = {! !}

-- type ascription `the A a : A`
the : (A : Type ℓ) → (a : A) → A
the A a = a
{-# INLINE the #-}

_≢_ : (a b : A) → Type _
a ≢ b = ¬ a ≡ b

≢-rec : ∀ {ℓB} {B : Type ℓB} {a b : A} → a ≡ b → a ≢ b → B
≢-rec eq neq = Empty.rec (neq eq)

isProp≢ : ∀ {a b : A} → isProp (a ≢ b)
isProp≢ {a} {b} p q i x = Empty.isProp⊥ (p x) (q x) i

module PathReasoning where
  ≡⟨⟩∎-syntax : ∀ (x y : A) → x ≡ y → x ≡ y
  ≡⟨⟩∎-syntax _ _ p = p
  {-# INLINE ≡⟨⟩∎-syntax #-}

  infixr 3 ≡⟨⟩∎-syntax
  syntax ≡⟨⟩∎-syntax x y p = x ≡⟨ p ⟩∎ y ∎

open PathReasoning using (≡⟨⟩∎-syntax) public

-- A step in equivalence reasoning for definitional identity equivalences
_≃⟨⟩_ : ∀ {ℓ ℓ'} (A : Type ℓ) {B : Type ℓ'} → A ≃ B → A ≃ B
A ≃⟨⟩ e = e
infixr 0 _≃⟨⟩_

symEquiv : ∀ {a b : A} → (a ≡ b) ≃ (b ≡ a)
symEquiv = strictEquiv sym sym

ℓ-of : ∀ {ℓ} (A : Type ℓ) → Level
ℓ-of {ℓ} _ = ℓ

ℓ-at : ∀ {ℓ} {A : Type ℓ} (a : A) → Level
ℓ-at {ℓ} _ = ℓ

-- Diagrammatic composition of functions (non-dependent)
_⨟_ : (f : A → B) (g : B → C) → A → C
f ⨟ g = λ a → g (f a)
infixl 9 _⨟_

-- Diagrammatic composition of functions (dependent)
_⨟ᴰ_ : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : A → Type ℓB} {C : ∀ a → B a → Type ℓC}
  → (f : (a : A) → B a)
  → (g : {a : A} → (b : B a) → C a b)
  → (a : A) → C a (f a)
f ⨟ᴰ g = λ a → g (f a)
infixl 9 _⨟ᴰ_

{- "Composition reasoning":

Write composites of functions without forgetting intermediate types.
Given f : A → B, g : B → C, e : C ≃ C', their composite A → C' is
  
  A →⟨ f ⟩ B →⟨ g ⟩ C →≃⟨ e ⟩ C' →∎
-}
_→⟨_⟩_ : (A : Type ℓ) → (A → B) → (B → C) → (A → C)
_ →⟨ f ⟩ g = f ⨟ g

_→≃⟨_⟩_ : (A : Type ℓ) → (A ≃ B) → (B → C) → (A → C)
_ →≃⟨ e ⟩ g = equivFun e ⨟ g

_→∎ : (A : Type ℓ) → A → A
A →∎ = λ a → a
{-# INLINE _→∎ #-}

infixr 0 _→⟨_⟩_
infixr 0 _→≃⟨_⟩_
infix 1 _→∎

isPropFromPointed→isProp : (A → isProp A) → isProp A
isPropFromPointed→isProp h a b = h a a b

isContr≃mereInh×isProp : isContr A ≃ (∥ A ∥₁ × isProp A)
isContr≃mereInh×isProp = propBiimpl→Equiv
  isPropIsContr
  (isProp× PT.isPropPropTrunc isPropIsProp)
  (λ is-contr-A → PT.∣ is-contr-A .fst ∣₁ , isContr→isProp is-contr-A)
  (uncurry $ PT.rec (isProp→ isPropIsContr) inhProp→isContr)

isContr≃inh×isProp : isContr A ≃ (A × isProp A)
isContr≃inh×isProp .fst is-contr-A = is-contr-A .fst , isContr→isProp is-contr-A
isContr≃inh×isProp .snd = isPointedTarget→isEquiv→isEquiv _ λ where
  (a₀ , is-prop-A) → equivIsEquiv $ propBiimpl→Equiv isPropIsContr (isProp× is-prop-A isPropIsProp) _ (uncurry inhProp→isContr)

⊤ : (ℓ : Level) → Type ℓ
⊤ _ = Unit*

ex-falso : Empty.⊥ → A
ex-falso ()

substAdjointEquiv : (B : A → Type ℓ) {x y : A} (p : x ≡ y)
  → {x′ : B x} {y′ : B y}
  → (subst B p x′ ≡ y′) ≃ (x′ ≡ subst B (sym p) y′)
substAdjointEquiv B {x} {y} p {x′} {y′} = invEquiv (equivAdjointEquiv (substEquiv' B p) {x′} {y′})

neqCongEquiv : {a b : A} {x y : B}
  → (a ≡ b) ≃ (x ≡ y)
  → (a ≢ b) ≃ (x ≢ y)
neqCongEquiv e = preCompEquiv (invEquiv e)

equivExt : {e f : A ≃ B} → (∀ x → equivFun e x ≡ equivFun f x) → e ≡ f
equivExt = equivEq ∘ funExt

-- equivPathP' : ∀ {ℓ ℓ′} {A : I → Type ℓ} {B : I → Type ℓ′}
--   → {e₀ : A i0 ≃ B i0} {e₁ : A i1 ≃ B i1}
--   → PathP (λ i → A i → B i) (equivFun e₀) (equivFun e₁)
--   → PathP (λ i → A i ≃ B i) e₀ e₁
-- equivPathP' {A} {B} {e₀} {e₁} p i .fst = p i
-- equivPathP' {A} {B} {e₀} {e₁} p i .snd .equiv-proof y = compᴵ (λ j → isContr (Σ[ x ∈ A (i ∧ j) ] PathP (λ k → B {! !}) (p (i ∧ j) x) y)) (∂ᴵ i) {! !}

contractDomainEquiv : isContr A → (A → B) ≃ B
contractDomainEquiv is-contr-A = isoToEquiv (isContr→Iso2 is-contr-A)

equivPathPEquiv : ∀ {ℓ ℓ′} {A : I → Type ℓ} {B : I → Type ℓ′}
  → {e₀ : A i0 ≃ B i0} {e₁ : A i1 ≃ B i1}
  → PathP (λ i → A i → B i) (equivFun e₀) (equivFun e₁) ≃ PathP (λ i → A i ≃ B i) e₀ e₁
equivPathPEquiv {A} {B} {e₀} {e₁} = isoToEquiv iso module equivPathPEquiv where
  iso : Iso _ _
  iso .Iso.fun = equivPathP
  iso .Iso.inv = congP (λ i → equivFun)
  iso .Iso.rightInv _ = ΣSquarePProp isPropIsEquiv refl
  iso .Iso.leftInv _ = refl

postCompFiberEquiv : (f : A → B) → (ψ : C → B) → (∀ c → fiber f (ψ c)) ≃ fiber (f ∘_) ψ
postCompFiberEquiv {A} {C} f ψ =
  (∀ c → Σ[ a ∈ A ] f a ≡ ψ c)
    ≃⟨ Σ-Π-≃ ⟩
  Σ[ φ ∈ (C → A) ] (∀ c → f (φ c) ≡ ψ c)
    ≃⟨ Σ-cong-equiv-snd (λ φ → funExtEquiv) ⟩
  Σ[ φ ∈ (C → A) ] f ∘ φ ≡ ψ
    ≃∎

private
  variable
    A′ : Type ℓ

Σ-contractSndIso : {B : A → Type ℓ} → (∀ a → isContr (B a)) → Iso (Σ A B) A
Σ-contractSndIso contr-snd .Iso.fun = fst
Σ-contractSndIso contr-snd .Iso.inv a = a , contr-snd a .fst
Σ-contractSndIso contr-snd .Iso.rightInv _ = refl
Σ-contractSndIso contr-snd .Iso.leftInv (a , b) = cong (a ,_) (contr-snd a .snd b)

module _ {ℓA ℓB ℓC ℓD} {A : Type ℓA} {B : A → Type ℓB} {C : ∀ a → B a → Type ℓC} {D : ∀ a → (b : B a) → (c : C a b) → Type ℓD} where
  Σ-Π₂-Iso : Iso ((a : A) → (b : B a) → Σ (C a b) (D a b)) (Σ[ f ∈ (∀ a → (b : B a) → C a b) ] ∀ a → (b : B a) → D a b (f a b))
  Σ-Π₂-Iso .Iso.fun f = (λ a b → f a b .fst) , (λ a b → f a b .snd)
  Σ-Π₂-Iso .Iso.inv (f , g) a b = f a b , g a b
  Σ-Π₂-Iso .Iso.rightInv _ = refl
  Σ-Π₂-Iso .Iso.leftInv _ = refl

  Σ-Π₂-≃ : ((a : A) → (b : B a) → Σ (C a b) (D a b)) ≃ (Σ[ f ∈ (∀ a → (b : B a) → C a b) ] ∀ a → (b : B a) → D a b (f a b))
  unquoteDef Σ-Π₂-≃ = defStrictIsoToEquiv Σ-Π₂-≃ Σ-Π₂-Iso
    
module _ {B′ : A′ → Type ℓ} where
  Σ-map-fst : (f : A → A′) → (Σ A (B′ ∘ f)) → (Σ A′ B′)
  Σ-map-fst f (a , b′) = (f a , b′)

  Σ-map-fst-fiber-iso : (f : A → A′)
    → {a′ : A′} {b′ : B′ a′}
    → Iso (fiber (Σ-map-fst f) (a′ , b′)) (fiber f a′)
  Σ-map-fst-fiber-iso {A} f {a′} {b′} =
    Σ[ (a , b) ∈ Σ A (B′ ∘ f) ] (f a , b) ≡ (a′ , b′)
      Iso⟨ shuffle ⟩
    Σ[ (a , p) ∈ fiber f a′ ] singlP (λ i → B′ (p (~ i))) b′
      Iso⟨ Σ-contractSndIso (λ _ → isContrSinglP _ b′) ⟩
    Σ[ a ∈ A ] f a ≡ a′
      ∎Iso
    where
      shuffle : Iso _ (Σ[ (a , p) ∈ Σ[ a ∈ A ] f a ≡ a′ ] Σ[ b ∈ B′ (f a) ] PathP (λ i → B′ (p (~ i))) b′ b)
      shuffle .Iso.fun ((a , b) , p) = (a , cong fst p) , b , cong snd (sym p)
      shuffle .Iso.inv ((a , p) , b , q) = (a , b) , λ i → p i , q (~ i)
      shuffle .Iso.rightInv _ = refl
      shuffle .Iso.leftInv _ = refl

isEquiv-∘ : ∀ {f : A → B} {g : B → C}
  → isEquiv g
  → isEquiv f
  → isEquiv (g ∘ f)
isEquiv-∘ {f} {g} is-equiv-g is-equiv-f = equivIsEquiv (compEquiv (f , is-equiv-f) (g , is-equiv-g))

module _ {ℓB ℓB′} {A : Type ℓ} {B : A → Type ℓB} {B′ : A → Type ℓB′} where
  Σ-map-snd : (f : ∀ a → B a → B′ a) → (Σ A B) → (Σ A B′)
  Σ-map-snd f (a , b) = (a , f a b)

  Σ-map-snd-fiber-iso : ∀ {f : ∀ a → B a → B′ a} {a′ : A} {b′ : B′ a′} → Iso (fiber (Σ-map-snd f) (a′ , b′)) (fiber (f a′) b′)
  Σ-map-snd-fiber-iso {f} {a′} {b′} = fiber-iso where
      shuffle : Iso _ (Σ[ (a , p) ∈ singl a′ ] Σ[ b ∈ B a ] PathP (λ i → B′ (p (~ i))) (f a b) b′)
      shuffle .Iso.fun ((a , b) , (p , q)) = (a , sym p) , b , q
      shuffle .Iso.inv ((a , p) , b , q) = (a , b) , sym p , q
      shuffle .Iso.rightInv _ = refl
      shuffle .Iso.leftInv _ = refl

      fiber-iso : Iso (fiber (Σ-map-snd f) (a′ , b′)) (fiber (f a′) b′)
      fiber-iso =
        _
          Iso⟨ Σ-cong-iso-snd (λ (a , b) → invIso ΣPathPIsoPathPΣ) ⟩
        Σ[ (a , b) ∈ Σ A B ] Σ[ p ∈ a ≡ a′ ] PathP (λ i → B′ (p i)) (f a b) b′
          Iso⟨ shuffle ⟩
        Σ[ (a , p) ∈ singl a′ ] Σ[ b ∈ B a ] PathP (λ i → B′ (p (~ i))) (f a b) b′
          Iso⟨ Σ-contractFstIso (isContrSingl a′) ⟩
        _
          ∎Iso

  isEquiv-Σ-map-snd : {f : ∀ a → B a → B′ a} → (∀ a → isEquiv (f a)) → isEquiv (Σ-map-snd f)
  isEquiv-Σ-map-snd {f} is-equiv-f .equiv-proof (a′ , b′) = isOfHLevelRetractFromIso 0 Σ-map-snd-fiber-iso (is-equiv-f a′ .equiv-proof b′)

  opaque
    isEquiv-Σ-map-snd→isEquiv : {f : ∀ a → B a → B′ a} → isEquiv (Σ-map-snd f) → ∀ a → isEquiv (f a)
    isEquiv-Σ-map-snd→isEquiv {f} is-equiv-Σ-map-snd a′ .equiv-proof b′ = isOfHLevelRetractFromIso 0
      (invIso Σ-map-snd-fiber-iso)
      (is-equiv-Σ-map-snd .equiv-proof (a′ , b′))

Σ-map : ∀ {ℓB ℓB′} {B : A → Type ℓB} {B′ : A′ → Type ℓB′}
  → (e : A → A′)
  → (f : ∀ a → B a → B′ (e a))
  → Σ A B → Σ A′ B′
Σ-map e f = Σ-map-snd f ⨟ Σ-map-fst e

isOfHLevelSucΣSndProp : ∀ {ℓB} {B : A → Type ℓB} (n : HLevel)
  → isOfHLevel (suc n) A
  → (∀ a → isProp (B a))
  → isOfHLevel (suc n) (Σ A B)
isOfHLevelSucΣSndProp n is-trunc-A is-prop-B = isOfHLevelΣ (suc n) is-trunc-A λ a → isProp→isOfHLevelSuc n (is-prop-B a)

Σ-swap-fst-≃ : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : Type ℓB} {C : A → B → Type ℓC}
  → (Σ[ a ∈ A ] Σ[ b ∈ B ] C a b) ≃(Σ[ b ∈ B ] Σ[ a ∈ A ] C a b)
Σ-swap-fst-≃ = strictEquiv (λ (a , b , c) → (b , a , c)) (λ (b , a , c) → (a , b , c))

hSet≡ : ∀ {X Y : hSet ℓ} → ⟨ X ⟩ ≡ ⟨ Y ⟩ → X ≡ Y
hSet≡ = Σ≡Prop (λ X → isPropIsSet)
