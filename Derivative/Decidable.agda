{-# OPTIONS --safe #-}
module Derivative.Decidable where

open import Derivative.Prelude

open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
import      Cubical.Data.Empty as Empty
import      Cubical.Data.Unit as Unit
open import Cubical.Relation.Nullary
open import Cubical.Foundations.GroupoidLaws using (lCancel)
open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary
  public
  using
    ( Dec ; yes ; no
    ; isPropDec
    ; Discrete
    ; ¬_
    ; isProp¬
    ; Discrete→isSet
    )
  renaming
    ( mapDec to map
    ; decRec to rec
    )
open import Cubical.Relation.Nullary.HLevels
  public
  using
    ( isPropDiscrete
    )

private
  variable
    ℓ : Level
    A B : Type ℓ

elim : ∀ {ℓB} {B : Dec A → Type ℓB}
  → (yes* : (a : A) → B (yes a))
  → (no* : (¬a : ¬ A) → B (no ¬a))
  → (a? : Dec A) → B a?
elim yes* no* (yes p) = yes* p
elim yes* no* (no ¬p) = no* ¬p

decNot : Dec A → Dec (¬ A)
decNot (yes p) = no λ ¬p → ¬p p
decNot (no ¬p) = yes ¬p

decEquiv : (e : A ≃ B) → Dec A → Dec B
decEquiv e = map (equivFun e) (_∘ invEq e)

Dec→Type : Dec A → Type
Dec→Type (yes _) = Unit.Unit
Dec→Type (no  _) = Empty.⊥

Dec→Type* : Dec A → Type ℓ
Dec→Type* (yes _) = Unit.Unit*
Dec→Type* (no  _) = Empty.⊥*

opaque
  Dec→Collapsible : Dec A → Collapsible A
  Dec→Collapsible = SplitSupport→Collapsible ∘ PStable→SplitSupport ∘ Stable→PStable ∘ Dec→Stable

isProp→Discrete : isProp A → Discrete A
isProp→Discrete is-prop x y = yes (is-prop x y)

Discrete→DiscretePath : Discrete A → (a b : A) → Discrete (a ≡ b)
Discrete→DiscretePath disc-A a b = isProp→Discrete (Discrete→isSet disc-A a b)

opaque
  locallyCollapsible→locallyIsPropPath : (a : A) → (∀ b → Collapsible (a ≡ b)) → (∀ b → isProp (a ≡ b))
  locallyCollapsible→locallyIsPropPath {A} a coll b p q =
    p ≡⟨ conj b p ⟩
    sym (collapse a refl) ∙ collapse b p ≡⟨ cong (sym (collapse a refl) ∙_) (is-2-const-collapse b p q) ⟩
    sym (collapse a refl) ∙ collapse b q ≡⟨ sym $ conj b q ⟩
    q ∎
    where
      module _ (b : A) where
        collapse : a ≡ b → a ≡ b
        collapse = fst (coll b)

        is-2-const-collapse : (p q : a ≡ b) → collapse p ≡ collapse q
        is-2-const-collapse = snd (coll b)

      conj : ∀ b → (p : a ≡ b) → p ≡ sym (collapse a refl) ∙ collapse b p
      conj b = J (λ b p → p ≡ sym (collapse a refl) ∙ collapse b p) $ sym (lCancel (collapse a refl))

  -- A local version of Hedberg's theorem:
  -- Given (a : A), if equality with `a` is decidable, then paths to `a` are unique if they exist.
  locallyDiscrete→locallyIsPropPath : (a : A) → (∀ b → Dec (a ≡ b)) → (∀ b → isProp (a ≡ b))
  locallyDiscrete→locallyIsPropPath a disc = locallyCollapsible→locallyIsPropPath a λ b → Dec→Collapsible (disc b)


dec-⊎-equiv : Dec A ≃ (A ⊎ (¬ A))
dec-⊎-equiv = isoToEquiv iso module dec-⊎-equiv where
  iso : Iso _ _
  iso .Iso.fun (yes p) = inl p
  iso .Iso.fun (no ¬p) = inr ¬p
  iso .Iso.inv (inl x) = yes x
  iso .Iso.inv (inr x) = no x
  iso .Iso.rightInv (inl x) = refl
  iso .Iso.rightInv (inr x) = refl
  iso .Iso.leftInv (yes p) = refl
  iso .Iso.leftInv (no ¬p) = refl

module DecPath where
  Cover : Dec A → Dec A → Type _
  Cover (yes p) (yes q) = p ≡ q
  Cover (yes p) (no ¬q) = Empty.⊥*
  Cover (no ¬p) (yes q) = Empty.⊥*
  Cover (no ¬p) (no ¬q) = ⊤ _

  reflCode : (x : Dec A) → Cover x x
  reflCode (yes p) = refl
  reflCode (no ¬p) = tt*

  encode : (x y : Dec A) → x ≡ y → Cover x y
  encode x _ = J (λ y p → Cover x y) $ reflCode x

  encodeRefl : (x : Dec A) → encode x x refl ≡ reflCode x
  encodeRefl x = JRefl (λ y p → Cover x y) $ reflCode x

  decode : (x y : Dec A) → Cover x y → x ≡ y
  decode (yes p) (yes q) p≡q = cong yes p≡q
  decode (no ¬p) (no ¬q) _ = cong no $ isProp¬ _ ¬p ¬q

  decodeRefl : (x : Dec A) → decode x x (reflCode x) ≡ refl
  decodeRefl (yes p) = refl
  decodeRefl {A} (no ¬p) i j = no (isContr→isProp (isProp→isContrPath (isProp¬ A) ¬p ¬p) (isProp¬ _ ¬p ¬p) refl i j)

  decode-encode : (x y : Dec A) → ∀ p → decode x y (encode x y p) ≡ p
  decode-encode x y = J (λ y p → decode x y (encode x y p) ≡ p) $ cong (decode x x) (encodeRefl x) ∙ decodeRefl x

  encode-decode : (x y : Dec A) → ∀ c → encode x y (decode x y c) ≡ c
  encode-decode (yes p) (yes q) c = J (λ y c → encode _ _ (cong yes c) ≡ c) (encodeRefl (yes p)) c
  encode-decode (no ¬p) (no ¬q) c = refl′ c

  Cover≃Path : (x y : Dec A) → Cover x y ≃ (x ≡ y)
  Cover≃Path x y = isoToEquiv λ where
    .Iso.fun → decode x y
    .Iso.inv → encode x y
    .Iso.leftInv → encode-decode x y
    .Iso.rightInv → decode-encode x y

isEmbeddingYes : isEmbedding {A = A} yes
isEmbeddingYes w z = equivIsEquiv (DecPath.Cover≃Path (yes w) (yes z))
