{-# OPTIONS --safe #-}
module Derivative.Basics.Sigma where

open import Derivative.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels using (isSet→SquareP)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level
    A A′ : Type ℓ

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

  isEquiv-Σ-map-fst : {f : A → A′} → isEquiv f → isEquiv (Σ-map-fst f)
  isEquiv-Σ-map-fst {f} is-equiv-f .equiv-proof (a′ , b′) = isOfHLevelRetractFromIso 0
    (Σ-map-fst-fiber-iso f)
    (is-equiv-f .equiv-proof a′)

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

isEquiv-Σ-map : ∀ {ℓB ℓB′} {B : A → Type ℓB} {B′ : A′ → Type ℓB′}
  → {e : A → A′}
  → {f : ∀ a → B a → B′ (e a)}
  → isEquiv e → (∀ a → isEquiv (f a))
  → isEquiv (Σ-map {B′ = B′} e f)
isEquiv-Σ-map {e} {f} is-equiv-e is-equiv-f =
  isEquiv-∘
    {f = Σ-map-snd f}
    {g = Σ-map-fst e}
    (isEquiv-Σ-map-fst is-equiv-e)
    (isEquiv-Σ-map-snd is-equiv-f)

isOfHLevelSucΣSndProp : ∀ {ℓB} {B : A → Type ℓB} (n : HLevel)
  → isOfHLevel (suc n) A
  → (∀ a → isProp (B a))
  → isOfHLevel (suc n) (Σ A B)
isOfHLevelSucΣSndProp n is-trunc-A is-prop-B = isOfHLevelΣ (suc n) is-trunc-A λ a → isProp→isOfHLevelSuc n (is-prop-B a)

Σ-swap-fst-≃ : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : Type ℓB} {C : A → B → Type ℓC}
  → (Σ[ a ∈ A ] Σ[ b ∈ B ] C a b) ≃(Σ[ b ∈ B ] Σ[ a ∈ A ] C a b)
Σ-swap-fst-≃ = strictEquiv (λ (a , b , c) → (b , a , c)) (λ (b , a , c) → (a , b , c))

module _
  {A : I → I → Type ℓ}
  {B : (i j : I) → A i j → Type ℓ'}
  {x₀₀ : Σ (A i0 i0) (B i0 i0)}
  {x₀₁ : Σ (A i0 i1) (B i0 i1)}
  {x₀₋ : PathP (λ j → Σ (A i0 j) (B i0 j)) x₀₀ x₀₁}
  {x₁₀ : Σ (A i1 i0) (B i1 i0)}
  {x₁₁ : Σ (A i1 i1) (B i1 i1)}
  {x₁₋ : PathP (λ j → Σ (A i1 j) (B i1 j)) x₁₀ x₁₁}
  {x₋₀ : PathP (λ i → Σ (A i i0) (B i i0)) x₀₀ x₁₀}
  {x₋₁ : PathP (λ i → Σ (A i i1) (B i i1)) x₀₁ x₁₁}
  where

  fstP : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
    → {x₀ : Σ (A i0) (B i0)}
    → {x₁ : Σ (A i1) (B i1)}
    → PathP (λ i → Σ (A i) (B i)) x₀ x₁
    → PathP A (fst x₀) (fst x₁)
  fstP p = λ i → fst (p i)
  {-# INLINE fstP #-}

  sndP : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
    → {x₀ : Σ (A i0) (B i0)}
    → {x₁ : Σ (A i1) (B i1)}
    → (p : PathP (λ i → Σ (A i) (B i)) x₀ x₁)
    → PathP (λ i → B i (fstP p i)) (snd x₀) (snd x₁)
  sndP p = λ i → snd (p i)
  {-# INLINE sndP #-}

  ΣSquareP :
    Σ[ sq ∈ SquareP A (fstP x₀₋) (fstP x₁₋) (fstP x₋₀) (fstP x₋₁) ]
      SquareP (λ i j → B i j (sq i j)) (sndP x₀₋) (sndP x₁₋) (sndP x₋₀) (sndP x₋₁)
    → SquareP (λ i j → Σ (A i j) (B i j)) x₀₋ x₁₋ x₋₀ x₋₁
  ΣSquareP sq = λ i j → (sq .fst i j) , (sq .snd i j)

  ΣSquarePProp : ((a : A i1 i1) → isProp (B i1 i1 a))
    → SquareP A (fstP x₀₋) (fstP x₁₋) (fstP x₋₀) (fstP x₋₁)
    → SquareP (λ i j → Σ (A i j) (B i j)) x₀₋ x₁₋ x₋₀ x₋₁
  fst (ΣSquarePProp propB₁₁ sqA i j) = sqA i j
  snd (ΣSquarePProp propB₁₁ sqA i j) = sqB i j where
    propB : (i j : I) → isProp (B i j (sqA i j))
    propB i j = transport (λ k → isProp (B (~ k ∨ i) (~ k ∨ j) (sqA (~ k ∨ i) (~ k ∨ j)))) (propB₁₁ (sqA i1 i1))

    sqB : SquareP (λ i j → B i j (sqA i j)) (sndP x₀₋) (sndP x₁₋) (sndP x₋₀) (sndP x₋₁)
    sqB = isProp→SquareP (λ i j → propB i j) _ _ _ _

  ΣSquarePSet : ((a : A i1 i1) → isSet (B i1 i1 a))
    → SquareP A (fstP x₀₋) (fstP x₁₋) (fstP x₋₀) (fstP x₋₁)
    → SquareP (λ i j → Σ (A i j) (B i j)) x₀₋ x₁₋ x₋₀ x₋₁
  ΣSquarePSet is-set-B₁₁ sqA i j .fst = sqA i j
  ΣSquarePSet is-set-B₁₁ sqA i j .snd = sqB i j where
    is-set-B : (i j : I) → isSet (B i j (sqA i j))
    is-set-B i j = transport (λ k → isSet (B (~ k ∨ i) (~ k ∨ j) (sqA (~ k ∨ i) (~ k ∨ j)))) (is-set-B₁₁ (sqA i1 i1))

    sqB : SquareP (λ i j → B i j (sqA i j)) (sndP x₀₋) (sndP x₁₋) (sndP x₋₀) (sndP x₋₁)
    sqB = isSet→SquareP (λ i j → is-set-B i j) _ _ _ _

ΣSquare : {A : Type ℓ} {B : A → Type ℓ'}
  {x₀₀ x₀₁ : Σ A B}
  {x₀₋ : x₀₀ ≡ x₀₁}
  {x₁₀ x₁₁ : Σ A B}
  {x₁₋ : x₁₀ ≡ x₁₁}
  {x₋₀ : x₀₀ ≡ x₁₀}
  {x₋₁ : x₀₁ ≡ x₁₁}
  → Σ[ sq ∈ Square (cong fst x₀₋) (cong fst x₁₋) (cong fst x₋₀) (cong fst x₋₁) ]
      SquareP (λ i j → B (sq i j)) (cong snd x₀₋) (cong snd x₁₋) (cong snd x₋₀) (cong snd x₋₁)
  → Square x₀₋ x₁₋ x₋₀ x₋₁
ΣSquare {A = A} {B = B} = ΣSquareP {A = λ _ _ → A} {B = λ _ _ → B}

ΣSquareProp : {A : Type ℓ} {B : A → Type ℓ'}
  → (∀ a → isProp (B a))
  → {x₀₀ x₀₁ : Σ A B}
  → {x₀₋ : x₀₀ ≡ x₀₁}
  → {x₁₀ x₁₁ : Σ A B}
  → {x₁₋ : x₁₀ ≡ x₁₁}
  → {x₋₀ : x₀₀ ≡ x₁₀}
  → {x₋₁ : x₀₁ ≡ x₁₁}
  → Square (cong fst x₀₋) (cong fst x₁₋) (cong fst x₋₀) (cong fst x₋₁)
  → Square x₀₋ x₁₋ x₋₀ x₋₁
ΣSquareProp {A = A} {B = B} propB = ΣSquarePProp {A = λ _ _ → A} {B = λ _ _ → B} propB
