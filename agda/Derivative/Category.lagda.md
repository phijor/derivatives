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

## Categorical structure on containers and linear maps

```agda
module Derivative.Category (ℓ : Level) where
```

### Categories of containers

Containers and linear morphisms carry the structure of a _wild_ category.
Composition of morphisms is unital and associative,
but the type of morphisms is in general not an \( h \)-set.
```agda
ℂont⊸∞ : WildCat (ℓ-suc ℓ) ℓ
ℂont⊸∞ .WildCat.ob = Container ℓ ℓ
ℂont⊸∞ .WildCat.Hom[_,_] = _⊸_
ℂont⊸∞ .WildCat.id {x = F} = id F
ℂont⊸∞ .WildCat._⋆_ = _⋆_
ℂont⊸∞ .WildCat.⋆IdL F = ⊸≡ refl $ funExt λ s → equivEq refl
ℂont⊸∞ .WildCat.⋆IdR F = ⊸≡ refl $ funExt λ s → equivEq refl
ℂont⊸∞ .WildCat.⋆Assoc F G H = ⊸≡ refl $ funExt λ s → equivEq refl
```

However, set-truncated containers _do_ form a proper 1-category.
```agda
ℂont⊸ : Category (ℓ-suc ℓ) ℓ
ℂont⊸ .Category.ob = SetContainer ℓ ℓ
ℂont⊸ .Category.Hom[_,_] = _⊸set_
ℂont⊸ .Category.id = id _
ℂont⊸ .Category._⋆_ = _⋆_
ℂont⊸ .Category.⋆IdL F = ⊸≡ refl $ funExt λ s → equivEq refl
ℂont⊸ .Category.⋆IdR F = ⊸≡ refl $ funExt λ s → equivEq refl
ℂont⊸ .Category.⋆Assoc F G H = ⊸≡ refl $ funExt λ s → equivEq refl
ℂont⊸ .Category.isSetHom {x = F} {y = G} = isOfHLevel-⊸ 2 {F} {G}
```

### The derivative functor

\( ∂ \) induces a wild functor on containers:
```agda
∂∞ : WildFunctor ℂont⊸∞ ℂont⊸∞
∂∞ .WildFunctor.F-ob = ∂.∂
∂∞ .WildFunctor.F-hom = ∂.∂[_]
∂∞ .WildFunctor.F-id = ⊸≡ (funExt λ { (s , p , _) → ΣPathP (refl′ s , Isolated≡ (refl′ p)) }) $ funExt λ (s , p , _) → equivExt λ (p' , _) → Remove≡ (refl′ p')
∂∞ .WildFunctor.F-seq f g = ⊸≡ (funExt λ _ → ΣPathP (refl , Isolated≡ refl)) $ funExt λ _ → equivExt λ _ → Remove≡ refl
```

Again, if restricted to set-containers, this is a functor of 1-categories.
```agda
∂ₛ : Functor ℂont⊸ ℂont⊸
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
open UnitCounit {C = ℂont⊸} {D = ℂont⊸}
open TriangleIdentities using (Δ₁ ; Δ₂)
```
-->

In [`Derivative.Adjunction`](Derivative.Adjunction.html), we construct the ingredients of a wild adjunction \( \_ ⊗ \mathsf{Id} ⊣ ∂ \).
Let us assemble these parts.
First, we ensure that \( \_ ⊗ \mathsf{Id} \) is a (wild) endofunctor:
```agda
-⊗Id : WildFunctor ℂont⊸∞ ℂont⊸∞
-⊗Id .WildFunctor.F-ob = _⊗Id
-⊗Id .WildFunctor.F-hom = [_]⊗Id
-⊗Id .WildFunctor.F-id = ⊸≡ refl $ funExt λ s → equivExt λ { (just s) → refl ; nothing → refl }
-⊗Id .WildFunctor.F-seq f g = ⊸≡ refl $ funExt λ s → equivExt λ { (just s) → refl ; nothing → refl }

_⊗Idₛ : SetContainer ℓ ℓ → SetContainer ℓ ℓ
((F , is-set-shape , is-set-pos) ⊗Idₛ) .fst = F ⊗Id
((F , is-set-shape , is-set-pos) ⊗Idₛ) .snd .fst = isSet× is-set-shape isSet-𝟙*
((F , is-set-shape , is-set-pos) ⊗Idₛ) .snd .snd (s , _) = isSet⊎ (is-set-pos s) isSet-𝟙*
```

Then, we verify that this indeed is a wild adjunction \( \_ ⊗ \mathsf{Id} ⊣ ∂ \):
```agda
open import Derivative.Basics.WildCategories using (_⊣∞_ ; WildAdjunction)

⊗Id-∂-wild-adjunction : -⊗Id ⊣∞ ∂∞
⊗Id-∂-wild-adjunction .WildAdjunction.η = unit
⊗Id-∂-wild-adjunction .WildAdjunction.ε = counit
⊗Id-∂-wild-adjunction .WildAdjunction.η-is-natural = is-natural-unit _ _
⊗Id-∂-wild-adjunction .WildAdjunction.ε-is-natural = is-natural-counit _ _
⊗Id-∂-wild-adjunction .WildAdjunction.zig = zig≡
⊗Id-∂-wild-adjunction .WildAdjunction.zag = zag≡
```

If we restrict this to set-truncated containers, we obtain an ordinary adjunction of functors of 1-categories:
```agda
-⊗Idₛ : Functor ℂont⊸ ℂont⊸
-⊗Idₛ .Functor.F-ob = _⊗Idₛ
-⊗Idₛ .Functor.F-hom = [_]⊗Id
-⊗Idₛ .Functor.F-id = -⊗Id .WildFunctor.F-id
-⊗Idₛ .Functor.F-seq = -⊗Id .WildFunctor.F-seq

η : 𝟙⟨ ℂont⊸ ⟩ ⇒ ∂ₛ ∘F -⊗Idₛ
η .NatTrans.N-ob (F , _) = unit F
η .NatTrans.N-hom f = sym (is-natural-unit _ _ f)

ε : -⊗Idₛ ∘F ∂ₛ ⇒ 𝟙⟨ ℂont⊸ ⟩
ε .NatTrans.N-ob (G , _) = counit G
ε .NatTrans.N-hom f = is-natural-counit _ _ f

⊗Id-∂-adjunction : -⊗Idₛ ⊣ ∂ₛ
⊗Id-∂-adjunction ._⊣_.η = η
⊗Id-∂-adjunction ._⊣_.ε = ε
⊗Id-∂-adjunction ._⊣_.triangleIdentities .Δ₁ (F , _) = zig≡ F
⊗Id-∂-adjunction ._⊣_.triangleIdentities .Δ₂ (G , _) = zag≡ G
```

From this we extract the (natural) equivalence of hom-sets \( (F ⊸ ∂ G) ≃ (F ⊗ \mathsf{Id} ⊸ G) \).
```agda
private
  _⊸ₛ_ = _⊸set_

⊸-equiv : (F G : SetContainer ℓ ℓ) → (F ⊸ₛ (∂ₛ.ob G)) ≃ ((F ⊗Idₛ) ⊸ₛ G)
⊸-equiv F G .fst f = [ f ]⊗Id ⋆ counit (G .fst)
⊸-equiv F G .snd = isoToIsEquiv (invIso iso) where

  nat-hom-adj : NaturalBijection._⊣_ -⊗Idₛ ∂ₛ
  nat-hom-adj = adj→adj' -⊗Idₛ ∂ₛ ⊗Id-∂-adjunction

  iso : Iso ((F ⊗Idₛ) ⊸ₛ G) (F ⊸ₛ (∂ₛ.ob G))
  iso = nat-hom-adj .NaturalBijection._⊣_.adjIso {c = F} {d = G}
```
