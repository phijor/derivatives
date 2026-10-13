{-# OPTIONS --safe #-}
open import Derivative.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor using (WildFunctor)

module Derivative.Basics.WildCategories
  {ℓo ℓh} {C D : WildCat ℓo ℓh}
  (F : WildFunctor C D)
  (G : WildFunctor D C)
  where
  private
    module C = WildCat C
    module D = WildCat D

    open WildFunctor F using () renaming (F-ob to F₀ ; F-hom to F₁)
    open WildFunctor G using () renaming (F-ob to G₀ ; F-hom to G₁)

  record WildAdjunction : Type (ℓ-max ℓo ℓh) where
    field
      η : ∀ x → C.Hom[ x , G₀ (F₀ x) ]
      ε : ∀ y → D.Hom[ F₀ (G₀ y) , y ]

      η-is-natural : ∀ {x y} (f : C.Hom[ x , y ])
        → η x C.⋆ (G₁ (F₁ f)) ≡ f C.⋆ η y

      ε-is-natural : ∀ {x y} (g : D.Hom[ x , y ])
        → (F₁ (G₁ g)) D.⋆ ε y ≡ ε x D.⋆ g

      zig : ∀ x → F₁ (η x) D.⋆ ε (F₀ x) ≡ D.id
      zag : ∀ y → η (G₀ y) C.⋆ G₁ (ε y) ≡ C.id

  _⊣∞_ : Type _
  _⊣∞_ = WildAdjunction
