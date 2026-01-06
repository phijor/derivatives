{-# OPTIONS -WnoUnsupportedIndexedMatch --safe #-}
module Derivative.Basics.W where

open import Derivative.Prelude
open import Derivative.Basics.Decidable
open import Derivative.Basics.Embedding
open import Derivative.Basics.Sigma
open import Derivative.Basics.Sum

open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma.Properties
open import Cubical.Relation.Nullary.Properties using (EquivPresDiscrete)
open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv

private
  variable
    ℓS ℓP ℓQ : Level

private
  module impl (S : Type ℓS) (P : S → Type ℓP) where
    data W : Type (ℓ-max ℓS ℓP) where
      sup : (s : S) (f : P s → W) → W

  module implᴰ (S : Type ℓS) (P : S → Type ℓP) (Q : S → Type ℓQ) where
    open impl S P

    data Wᴰ : W → Type (ℓ-max ℓQ (ℓ-of W)) where
      top : {s : S} {f : P s → W} → (q : Q s) → Wᴰ (sup s f)
      below : {s : S} {f : P s → W} → (p : P s) → (wᴰ : Wᴰ (f p)) → Wᴰ (sup s f)

module _ {S : Type ℓS} {P : S → Type ℓP} where
  open impl S P

  W-elim : ∀ {ℓ} {B : W → Type ℓ}
    → (sup* : (s : S) (f : P s → W) → (sup* : (p : P s) → B (f p)) → B (sup s f))
    → (w : W) → B w
  W-elim {B} sup* (sup s f) = sup* s f λ p → W-elim {B = B} sup* (f p)

  W-elim2 : ∀ {ℓ} {B : W → W → Type ℓ}
    → (sup* : (s₀ s₁ : S) (f₀ : P s₀ → W) (f₁ : P s₁ → W)
      → (sup* : (p₀ : P s₀) → (p₁ : P s₁) → B (f₀ p₀) (f₁ p₁))
      → B (sup s₀ f₀) (sup s₁ f₁)
      )
    → (w₀ w₁ : W) → B w₀ w₁
  W-elim2 {B} sup* (sup s₀ f₀) (sup s₁ f₁) = sup* s₀ s₁ f₀ f₁ λ p₀ p₁ → W-elim2 {B = B} sup* (f₀ p₀) (f₁ p₁)

  W-out : W → (Σ[ s ∈ S ] (P s → W))
  W-out (sup s f) = s , f

  W-shape : W → S
  W-shape = fst ∘ W-out

  W-branch : (w : W) → P (W-shape w) → W
  W-branch = snd ∘ W-out

  W-in : (Σ[ s ∈ S ] (P s → W)) → W
  W-in = uncurry sup

  W-in-equiv : (Σ[ s ∈ S ] (P s → W)) ≃ W
  W-in-equiv = isoToEquiv iso module W-in-equiv where
    iso : Iso (Σ[ s ∈ S ] (P s → W)) W
    iso .Iso.fun = W-in
    iso .Iso.inv = W-out
    iso .Iso.rightInv (sup s f) = refl
    iso .Iso.leftInv _ = refl

  W-rec : ∀ {ℓ} {A : Type ℓ}
    → (sup* : (Σ[ s ∈ S ] (P s → A)) → A)
    → W → A
  W-rec {A} sup* (sup s f) = sup* (s , λ p → W-rec sup* (f p))

  W-rec-β : ∀ {ℓ} {A : Type ℓ}
    → (sup* : (Σ[ s ∈ S ] (P s → A)) → A)
    → W-rec sup* ≡ W-out ⨟ Σ-map-snd (λ _ → W-rec sup* ∘_) ⨟ sup*
  W-rec-β sup* = funExt λ { (sup _ _ ) → refl }

  W-out-equiv : W ≃ (Σ[ s ∈ S ] (P s → W))
  W-out-equiv = isoToEquiv (invIso W-in-equiv.iso)

  W-out-unique : ∀ {ℓ} {A : Type ℓ} (f : (Σ[ s ∈ S ] (P s → A)) → A) → ∃![ f* ∈ (W → A) ] f* ≡ W-out ⨟ Σ-map-snd (λ s → f* ∘_) ⨟ f
  W-out-unique f .fst = W-rec f , W-rec-β f
  W-out-unique f .snd (f* , comm*) = ΣPathP (goal , goal-coh) module W-out-unique where
    goal-ext : ∀ w → W-rec f w ≡ f* w
    goal-ext (sup s x) = p ∙ q
      module goal-ext where
        p = cong (λ - → f (s , - )) (funExt (goal-ext ∘ x))
        q = sym (comm* ≡$ sup s x)

        filler = compPath-filler p q

    goal : W-rec f ≡ f*
    goal = funExt goal-ext

    goal-coh-ext : ∀ w → PathP (λ i → goal i w ≡ (W-out ⨟ Σ-map-snd (λ _ → (goal i) ∘_) ⨟ f) w) (W-rec-β f ≡$ w) (comm* ≡$ w)
    goal-coh-ext (sup s x) i j = goal-ext.filler s x (~ j) i
 
    goal-coh : PathP (λ i → goal i ≡ W-out ⨟ Σ-map-snd (λ _ → (goal i) ∘_) ⨟ f) (W-rec-β f) comm*
    goal-coh i j x = goal-coh-ext x i j
 
module _ {S : Type ℓS} {P : S → Type ℓP} where
  open impl
  WPath : (x y : W S P) → Type (ℓ-max ℓS ℓP)
  WPath (sup s₀ f₀) (sup s₁ f₁) = Σ (s₀ ≡ s₁) λ p → PathP (λ i → P (p i) → W S P) f₀ f₁

  ≡→WPath : (x y : W S P) → x ≡ y → WPath x y
  ≡→WPath (sup s₀ f₀) (sup s₁ f₁) x≡y .fst = cong W-shape x≡y
  ≡→WPath (sup s₀ f₀) (sup s₁ f₁) x≡y .snd = cong W-branch x≡y

  WPath→≡ : (x y : W S P) → WPath x y → x ≡ y
  WPath→≡ (sup s₀ f₀) (sup s₁ f₁) (s₀≡s₁ , f₀≡f₁) = cong₂ sup s₀≡s₁ f₀≡f₁

  WPath-linv-refl : (x : W S P) → WPath→≡ x x (≡→WPath x x refl) ≡ refl
  WPath-linv-refl (sup s f) = refl

  WPath-linv : (x y : W S P) (p : x ≡ y) → WPath→≡ _ _ (≡→WPath _ _ p) ≡ p
  WPath-linv x y = J (λ y p → WPath→≡ _ _ (≡→WPath _ _ p) ≡ p) $ WPath-linv-refl x

  WPath-rinv : (x y : W S P) (p : WPath x y) → ≡→WPath _ _ (WPath→≡ _ _ p) ≡ p
  WPath-rinv (sup s₀ f₀) (sup s₁ f₁) _ = refl

  WPathIso : (x y : W S P) → Iso (x ≡ y) (WPath x y)
  WPathIso x y .Iso.fun = ≡→WPath _ _
  WPathIso x y .Iso.inv = WPath→≡ _ _
  WPathIso x y .Iso.rightInv = WPath-rinv _ _
  WPathIso x y .Iso.leftInv = WPath-linv _ _

  WPath-≃ : (x y : W S P) → (x ≡ y) ≃ (WPath x y)
  WPath-≃ x y = isoToEquiv $ WPathIso x y

module _ (S : Type ℓS) (P : S → Type ℓP) (Q : S → Type ℓQ) where
  open impl S P
  open implᴰ S P Q

  module _ (s : S) (f : P s → W) where
    Wᴰ-out : Wᴰ (sup s f) → Q s ⊎ (Σ[ p ∈ P s ] (Wᴰ (f p)))
    Wᴰ-out (top q) = inl q
    Wᴰ-out (below p wᴰ) = inr (p , wᴰ)

    Wᴰ-in : Q s ⊎ (Σ[ p ∈ P s ] (Wᴰ (f p))) → Wᴰ (sup s f)
    Wᴰ-in (inl q) = top q
    Wᴰ-in (inr (p , wᴰ)) = below p wᴰ

    Wᴰ-out-equiv : Wᴰ (sup s f) ≃ Q s ⊎ (Σ[ p ∈ P s ] (Wᴰ (f p)))
    Wᴰ-out-equiv = isoToEquiv iso module Wᴰ-out-equiv where
      iso : Iso _ _
      iso .Iso.fun = Wᴰ-out
      iso .Iso.inv = Wᴰ-in
      iso .Iso.rightInv (inl _) = refl
      iso .Iso.rightInv (inr _) = refl
      iso .Iso.leftInv (top _) = refl
      iso .Iso.leftInv (below _ _) = refl

    Wᴰ-in-equiv : Q s ⊎ (Σ[ p ∈ P s ] (Wᴰ (f p))) ≃ Wᴰ (sup s f)
    Wᴰ-in-equiv = isoToEquiv (invIso Wᴰ-out-equiv.iso)

    isEquiv-Wᴰ-in : isEquiv Wᴰ-in
    isEquiv-Wᴰ-in = equivIsEquiv Wᴰ-in-equiv

  module _ (disc-P : ∀ s → Discrete (P s)) (disc-Q : ∀ s → Discrete (Q s)) where
    discrete-Wᴰ : ∀ w → Discrete (Wᴰ w)
    discrete-Wᴰ (sup s f) = EquivPresDiscrete (Wᴰ-in-equiv s f) $
      discrete⊎
        (disc-Q s)
        (discreteΣ (disc-P s) (discrete-Wᴰ ∘ f))

  Wᴰ-Path : ∀ {w₀ w₁} (h : WPath w₀ w₁) → (x : Wᴰ w₀) → (y : Wᴰ w₁) → Type (ℓ-max ℓS (ℓ-max ℓP ℓQ))
  Wᴰ-Path (s₀≡s₁ , f₀≡f₁) (top q₀) (top q₁) = Lift {j = ℓ-max ℓS ℓP} $ PathP (λ i → Q (s₀≡s₁ i)) q₀ q₁
  Wᴰ-Path (s₀≡s₁ , f₀≡f₁) (top q₀) (below p₁ y) = 𝟘*
  Wᴰ-Path (s₀≡s₁ , f₀≡f₁) (below p₀ x) (top q₁) = 𝟘*
  Wᴰ-Path (s₀≡s₁ , f₀≡f₁) (below p₀ x) (below p₁ y)
    = Σ[ p₀≡p₁ ∈ PathP (λ i → P (s₀≡s₁ i)) p₀ p₁ ] PathP (λ i → Wᴰ (f₀≡f₁ i (p₀≡p₁ i))) x y

  Wᴰ-Path→≡ : ∀ {w₀ w₁} {p : WPath w₀ w₁} {x : Wᴰ w₀} {y : Wᴰ w₁} → Wᴰ-Path p x y → PathP (λ i → Wᴰ (WPath→≡ _ _ p i)) x y
  Wᴰ-Path→≡ {x = top q₀}     {y = top q₁}     (lift q) i = top (q i)
  Wᴰ-Path→≡ {x = below p₀ x} {y = below p₁ y} (p₀≡p₁ , x≡y) i = below (p₀≡p₁ i) (x≡y i)

open impl public using (W ; sup)
open implᴰ public using (Wᴰ ; top ; below)

W-map : ∀ {S S′ : Type ℓS} {P : S → Type ℓP} {P′ : S′ → Type ℓP}
  → (f : S → S′)
  → (fᴰ : ∀ s → P′ (f s) → P s)
  → W S P → W S′ P′
W-map f fᴰ = W-elim λ s x map → sup (f s) (map ∘ fᴰ s)

W-fiber-equiv : ∀ {ℓ} {S : Type ℓS} {P : S → Type ℓP} {Y : Type ℓ}
  → {f : W S P → Y}
  → (y : Y) → fiber f y ≃ (Σ[ s ∈ S ] fiber (f ∘ sup s) y)
W-fiber-equiv {S} {P} {Y} {f} y =
  Σ[ x ∈ W S P ] f x ≡ y
    ≃⟨ invEquiv $ Σ-cong-equiv-fst W-in-equiv ⟩
  Σ[ (s , x) ∈ Σ[ s ∈ S ] (P s → W S P) ] f (sup s x) ≡ y
    ≃⟨ Σ-assoc-≃ ⟩
  Σ[ s ∈ S ] Σ[ x ∈ (P s → W S P) ] f (sup s x) ≡ y
    ≃∎

isEmbedding→W-rec-fiber-equiv : ∀ {ℓ} {S : Type ℓS} {P : S → Type ℓP} {A : Type ℓ}
  → (sup* : (Σ[ s ∈ S ] (P s → A)) → A)
  → isEmbedding sup*
  → (s : S) (f : P s → W S P)
  → fiber (W-rec sup*) (W-rec sup* (sup s f)) ≃ ((p : P s) → fiber (W-rec sup*) (W-rec sup* (f p)))
isEmbedding→W-rec-fiber-equiv {S} {P} {A} sup* is-emb-sup* s f =
  Σ[ x ∈ W S P ] W-rec sup* x ≡ sup* (s , W-rec sup* ∘ f)
    ≃⟨ Σ-cong-equiv-snd (λ x → compPathlEquiv (sym $ W-rec-β sup* ≡$ x)) ⟩
  Σ[ x ∈ W S P ] sup* (W-out x .fst , _) ≡ sup* (s , W-rec sup* ∘ f)
    ≃⟨ Σ-cong-equiv-snd (λ x → invEquiv $ cong sup* , is-emb-sup* _ _) ⟩
  Σ[ w ∈ W S P ] (W-out w .fst , W-rec sup* ∘ W-out w .snd) ≡ (s , W-rec sup* ∘ f)
    ≃⟨ invEquiv $ Σ-cong-equiv-fst $ W-in-equiv ⟩
  Σ[ (s′ , f′) ∈ (Σ[ s ∈ S ] (P s → W S P)) ] (s′ , W-rec sup* ∘ f′) ≡ (s , W-rec sup* ∘ f)
    ≃⟨ Σ-cong-equiv-snd (λ _ → invEquiv ΣPathP≃PathPΣ) ⟩
  Σ[ (s′ , f′) ∈ (Σ[ s ∈ S ] (P s → W S P)) ] Σ _ _
    ≃⟨ strictEquiv
      (λ { ((s′ , f′) , s′≡s , f≡f′) → ((s′ , sym s′≡s) , (f′ , f≡f′)) })
      (λ { ((s′ , s≡s′) , (f′ , f≡f′)) → ((s′ , f′) , sym s≡s′ , f≡f′) })
    ⟩
  Σ[ (s′ , s≡s′) ∈ singl s ] Σ[ f′ ∈ (P s′ → W S P) ] PathP (λ i → P (s≡s′ (~ i)) → A) (W-rec sup* ∘ f′) (W-rec sup* ∘ f)
    ≃⟨ Σ-contractFst (isContrSingl s) ⟩
  Σ[ f′ ∈ (P s → W S P) ] (W-rec sup* ∘ f′) ≡ (W-rec sup* ∘ f)
    ≃⟨ Σ-cong-equiv-snd (λ f′ → invEquiv funExtEquiv) ⟩
  Σ[ f′ ∈ (P s → W S P) ] ((p : P s) → W-rec sup* (f′ p) ≡ W-rec sup* (f p))
    ≃⟨ invEquiv Σ-Π-≃ ⟩
  ((p : P s) → fiber (W-rec sup*) (W-rec sup* (f p)))
    ≃∎

isEmbedding-W-rec : ∀ {ℓ} {S : Type ℓS} {P : S → Type ℓP} {A : Type ℓ}
  → (sup* : (Σ[ s ∈ S ] (P s → A)) → A)
  → isEmbedding sup*
  → isEmbedding (W-rec sup*)
isEmbedding-W-rec {S} {P} {A} sup* is-emb-sup* = hasPropFibersOfImage→isEmbedding prop-fibers where
  fiber-equiv : ∀ s f → fiber (W-rec sup*) (W-rec sup* (sup s f)) ≃ ((p : P s) → fiber (W-rec sup*) (W-rec sup* (f p)))
  fiber-equiv = isEmbedding→W-rec-fiber-equiv sup* is-emb-sup*

  prop-fibers : ∀ w → isProp (fiber (W-rec sup*) (W-rec sup* w))
  prop-fibers (sup s f) = isOfHLevelRespectEquiv 1 (invEquiv $ fiber-equiv s f) is-prop-fibers'
    where
      is-prop-fibers' : isProp (∀ p → fiber (W-rec sup*) (W-rec sup* (f p)))
      is-prop-fibers' = isPropΠ λ p → prop-fibers (f p)
