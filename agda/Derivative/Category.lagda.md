<!--
```agda
{-# OPTIONS --safe #-}
open import Derivative.Prelude

open import Derivative.Basics.Maybe
open import Derivative.Basics.Sum
open import Derivative.Basics.Unit

open import Derivative.Container
open import Derivative.Isolated
open import Derivative.Remove
import      Derivative.Derivative as ∂
open import Derivative.Adjunction


open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base using (_⇒_ ; NatTrans)
open import Cubical.Categories.Adjoint
```
-->

## Categorical structure on containers and cartesian maps

```agda
module Derivative.Category (ℓ : Level) where
```

### Categories of containers

Containers and cartesian morphisms carry the structure of a _wild_ category.
Composition of morphisms is unital and associative,
but the type of morphisms is in general not an \( h \)-set.
```agda
ℂont∞ : WildCat (ℓ-suc ℓ) ℓ
ℂont∞ .WildCat.ob = Container ℓ ℓ
ℂont∞ .WildCat.Hom[_,_] = Cart
ℂont∞ .WildCat.id {x = F} = id F
ℂont∞ .WildCat._⋆_ = _⋆_
ℂont∞ .WildCat.⋆IdL F = Cart≡ refl $ funExt λ s → equivEq refl
ℂont∞ .WildCat.⋆IdR F = Cart≡ refl $ funExt λ s → equivEq refl
ℂont∞ .WildCat.⋆Assoc F G H = Cart≡ refl $ funExt λ s → equivEq refl
```

However, set-truncated containers _do_ form a proper 1-category.
```agda
ℂont : Category (ℓ-suc ℓ) ℓ
ℂont .Category.ob = SetContainer ℓ ℓ
ℂont .Category.Hom[_,_] = SetCart
ℂont .Category.id = id _
ℂont .Category._⋆_ = _⋆_
ℂont .Category.⋆IdL F = Cart≡ refl $ funExt λ s → equivEq refl
ℂont .Category.⋆IdR F = Cart≡ refl $ funExt λ s → equivEq refl
ℂont .Category.⋆Assoc F G H = Cart≡ refl $ funExt λ s → equivEq refl
ℂont .Category.isSetHom {x = F} {y = G} = isOfHLevelCart 2 {F} {G}
```

### The derivative functor

\( ∂ \) induces a wild functor on containers:
```agda
∂∞ : WildFunctor ℂont∞ ℂont∞
∂∞ .WildFunctor.F-ob = ∂.∂
∂∞ .WildFunctor.F-hom = ∂.∂[_]
∂∞ .WildFunctor.F-id = Cart≡ (funExt λ { (s , p , _) → ΣPathP (refl′ s , Isolated≡ (refl′ p)) }) $ funExt λ (s , p , _) → equivExt λ (p' , _) → Remove≡ (refl′ p')
∂∞ .WildFunctor.F-seq f g = Cart≡ (funExt λ _ → ΣPathP (refl , Isolated≡ refl)) $ funExt λ _ → equivExt λ _ → Remove≡ refl
```

Again, if restricted to set-containers, this is a functor of 1-categories.
```agda
∂ₛ : Functor ℂont ℂont
∂ₛ .Functor.F-ob = ob module ∂ₛ where
  ob : SetContainer ℓ ℓ → SetContainer ℓ ℓ
  ob (F , is-trunc-F) .fst = ∂.∂ F
  ob (F , is-trunc-F) .snd = ∂.isTruncatedDerivative 0 1 is-trunc-F
∂ₛ .Functor.F-hom = ∂.∂[_]
∂ₛ .Functor.F-id = ∂∞ .WildFunctor.F-id
∂ₛ .Functor.F-seq = ∂∞ .WildFunctor.F-seq
```

### Universal property of \( ∂ \)

<!--
```agda
open UnitCounit {C = ℂont} {D = ℂont}
open TriangleIdentities using (Δ₁ ; Δ₂)
```
-->

In [`Derivative.Adjunction`](Derivative.Adjunction.html), we construct a wild adjunction \( \_ ⊗ \mathsf{Id} ⊣ ∂ \).
Here, we show that this is an ordinary adjunction of functors of 1-categories, if restricted to set-truncated containers.
First, we ensure that \( \_ ⊗ \mathsf{Id} \) is an endofunctor:
```agda
_⊗Id₀ : SetContainer ℓ ℓ → SetContainer ℓ ℓ
((F , is-set-shape , is-set-pos) ⊗Id₀) .fst = F ⊗Id
((F , is-set-shape , is-set-pos) ⊗Id₀) .snd .fst = isSet× is-set-shape isSet-𝟙*
((F , is-set-shape , is-set-pos) ⊗Id₀) .snd .snd (s , _) = isSet⊎ (is-set-pos s) isSet-𝟙*

-⊗Id : Functor ℂont ℂont
-⊗Id .Functor.F-ob = _⊗Id₀
-⊗Id .Functor.F-hom = [_]⊗Id
-⊗Id .Functor.F-id = Cart≡ refl $ funExt λ s → equivExt λ { (just s) → refl ; nothing → refl }
-⊗Id .Functor.F-seq f g = Cart≡ refl $ funExt λ s → equivExt λ { (just s) → refl ; nothing → refl }
```

Then, we verify that the unit and counit are indeed proper natural transformations.
```agda
η : 𝟙⟨ ℂont ⟩ ⇒ ∂ₛ ∘F -⊗Id
η .NatTrans.N-ob (F , _) = unit F
η .NatTrans.N-hom f = sym (is-natural-unit _ _ f)

ε : -⊗Id ∘F ∂ₛ ⇒ 𝟙⟨ ℂont ⟩
ε .NatTrans.N-ob (G , _) = counit G
ε .NatTrans.N-hom f = is-natural-counit _ _ f
```

Finally, we use the zig-zag equations to assemble this into an adjunction.
```agda
-⊗Id⊣∂ : -⊗Id ⊣ ∂ₛ
-⊗Id⊣∂ ._⊣_.η = η
-⊗Id⊣∂ ._⊣_.ε = ε
-⊗Id⊣∂ ._⊣_.triangleIdentities .Δ₁ (F , _) = zig≡ F
-⊗Id⊣∂ ._⊣_.triangleIdentities .Δ₂ (G , _) = zag≡ G
```

From this we extract the (natural) equivalence of hom-sets \( (F ⊸ ∂ G) ≃ (F ⊗ \mathsf{Id} ⊸ G) \).
```agda
private
  _⊸ₛ_ = SetCart

cart-equiv : (F G : SetContainer ℓ ℓ) → (F ⊸ₛ (∂ₛ.ob G)) ≃ ((F ⊗Id₀) ⊸ₛ G)
cart-equiv F G .fst f = [ f ]⊗Id ⋆ counit (G .fst)
cart-equiv F G .snd = isoToIsEquiv (invIso iso) where

  nat-hom-adj : NaturalBijection._⊣_ -⊗Id ∂ₛ
  nat-hom-adj = adj→adj' -⊗Id ∂ₛ -⊗Id⊣∂

  iso : Iso ((F ⊗Id₀) ⊸ₛ G) (F ⊸ₛ (∂ₛ.ob G))
  iso = nat-hom-adj .NaturalBijection._⊣_.adjIso {c = F} {d = G}
```
