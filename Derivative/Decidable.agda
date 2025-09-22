module Derivative.Decidable where

open import Derivative.Prelude

open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
import      Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary
open import Cubical.Foundations.GroupoidLaws using (lCancel)

open import Cubical.Relation.Nullary
  public
  using
    ( Dec ; yes ; no
    ; isPropDec
    ; Discrete
    ; ¬_
    ; Discrete→isSet
    )
  renaming
    ( mapDec to map
    )

private
  variable
    ℓ : Level
    A : Type ℓ

_≢_ : (a b : A) → Type _
a ≢ b = ¬ a ≡ b

≢-rec : ∀ {ℓB} {B : Type ℓB} {a b : A} → a ≡ b → a ≢ b → B
≢-rec eq neq = Empty.rec (neq eq)

elim : ∀ {ℓB} {B : Dec A → Type ℓB}
  → (yes* : (a : A) → B (yes a))
  → (no* : (¬a : ¬ A) → B (no ¬a))
  → (a? : Dec A) → B a?
elim yes* no* (yes p) = yes* p
elim yes* no* (no ¬p) = no* ¬p

decNot : Dec A → Dec (¬ A)
decNot (yes p) = no λ ¬p → ¬p p
decNot (no ¬p) = yes ¬p

opaque
  Dec→Collapsible : Dec A → Collapsible A
  Dec→Collapsible = SplitSupport→Collapsible ∘ PStable→SplitSupport ∘ Stable→PStable ∘ Dec→Stable

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
