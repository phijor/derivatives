## Ordered Lists as a Container

<!--
```agda
{-# OPTIONS -WnoUnsupportedIndexedMatch --safe #-}
module Derivative.Examples.List where

open import Derivative.Prelude
open import Derivative.Basics.W
open import Derivative.Basics.Fin
open import Derivative.Basics.Sum
open import Derivative.Basics.Unit
open import Derivative.Isolated.Base
open import Derivative.Remove
open import Derivative.Indexed.Container hiding (_[_])
open import Derivative.Indexed.Derivative
open import Derivative.Indexed.Mu
open import Derivative.Indexed.MuRule

import Cubical.Data.Nat as Nat
import Cubical.Data.Sigma as Sigma
import Cubical.Data.Empty as Empty

open Container
```
-->

The container \( ((n : ℕ) \lhd [n]) \) represents the type of ordered lists.
The shape of a list is its length \( n \); such a list has \( n \) positions for data.
```agda
private
  [_] : ℕ → Type
  [ n ] = Fin n

List : Container ℓ-zero 𝟙
List .Shape = ℕ
List .Pos _ n = [ n ]
```

### Derivative { #derivative-of-list }

The derivative of the list container is the container of pairs of lists.
```agda
∂List : ∂• List ⧟ (List ⊗ List)
∂List = ∂-list-equiv where
```

Recall that pairs of lists have the following shapes and positions:
```agda
  _ : List ⊗ List ≡ ((ℕ × ℕ) ◁ λ _ (m , n) → [ m ] ⊎ [ n ])
  _ = refl
```
We build an equivalence with this container in two steps.
First, notice that positions \( [ n ] \) are discrete,
hence \( {[ n ]}^\circ \simeq [ n ] \), and we can write \( \partial(\mathsf{List}) \) as the following:
```agda
  List∙ : Container ℓ-zero 𝟙
  List∙ = (Σ[ n ∈ ℕ ] [ n ]) ◁ λ _ (n , k) → [ n ] ∖ k

  forget-isolated-pos : ∂• List ⧟ List∙
  forget-isolated-pos = ⧟-shape $ Sigma.Σ-cong-equiv-snd $ Discrete→IsolatedEquiv ∘ DiscreteFin
```

Next, observe that pairs of lists of length \( m \) and \( n \) correspond uniquely to lists of length \( m + 1 + n \) with a hole at position \( m \).
The map `hole` computes the position of the hole in a list of length \( m + 1 + n \), preceded by \( m \) and followed by \( n \) elements.
```agda
  open Nat using () renaming (_+_ to infixr 8 _+_)

  hole : (m n : ℕ) → [ m + 1 + n ]
  hole zero n = fzero
  hole (suc m) n = fsuc (hole m n)
```

This defines a map into the shapes of \( \partial(\mathsf{List}) \):
Glue two lists of lengths \( m \) and \( n \) together, with a hole in between.
```agda
  glue : ℕ × ℕ → Σ[ n ∈ ℕ ] [ n ]
  glue (m , n) = (m + 1 + n) , hole m n
```

In the other direction, split a list of length \( n \) at position \( k \) into the parts preceding and following \( k \).
```agda
  split : (n : ℕ) → (k : [ n ]) → ℕ × ℕ
  split (suc n) fzero = 0 , n
  split (suc n) (fsuc k) = let (m' , n') = split n k in suc m' , n'
```

Together, these form an equivalence of shapes.
```agda
  glue-equiv : (ℕ × ℕ) ≃ (Σ[ n ∈ ℕ ] [ n ])
  glue-equiv = isoToEquiv glue-iso where
    split-glue : ∀ m n → split (m + 1 + n) (hole m n) ≡ (m , n)
    split-glue zero n = refl
    split-glue (suc m) n i = let (p , q) = split-glue m n i in suc p , q

    glue-split : ∀ n (k : [ n ]) → glue (split n k) ≡ (n , k)
    glue-split (suc n) fzero = refl
    glue-split (suc n) (fsuc k) i = let (p , q) = glue-split n k i in suc p , fsuc q

    glue-iso : Iso _ _
    glue-iso .Iso.fun = glue
    glue-iso .Iso.inv = uncurry split
    glue-iso .Iso.rightInv (k , p) = glue-split k p
    glue-iso .Iso.leftInv (m , n) = split-glue m n
```

We can now define the equivalence on positions:
Removing the hole from a list of length \( m + 1 + n \) leaves exactly the
positions of the two lists surrounding it.
```agda
  hole-remove : ∀ m n → ([ m + 1 + n ] ∖ hole m n) ≃ ([ m ] ⊎ [ n ])
  hole-remove zero n =
    (𝟙 ⊎ [ n ]) ∖ fzero
      ≃⟨ invEquiv remove-left-equiv ⟩
    (𝟙 ∖ •) ⊎ [ n ]
      ≃⟨ ⊎-left-≃ remove-• ⟩
    𝟘 ⊎ [ n ]
      ≃∎
    where
    remove-• : (𝟙 ∖ •) ≃ 𝟘
    remove-• = isProp→remove-empty-equiv isProp-𝟙* •
  hole-remove (suc m) n =
    (𝟙 ⊎ [ m + 1 + n ]) ∖ fsuc (hole m n)
      ≃⟨ invEquiv remove-right-equiv ⟩
    𝟙 ⊎ ([ m + 1 + n ] ∖ hole m n)
      ≃⟨ ⊎-right-≃ (hole-remove m n) ⟩
    𝟙 ⊎ ([ m ] ⊎ [ n ])
      ≃⟨ invEquiv ⊎-assoc-≃ ⟩
    (𝟙 ⊎ [ m ]) ⊎ [ n ]
      ≃∎
```

Thus, lists with a hole correspond exactly to pairs of lists.
```agda
  glue-at-hole : (List ⊗ List) ⧟ List∙
  glue-at-hole .Equiv.shape = glue-equiv
  glue-at-hole .Equiv.pos _ (m , n) = hole-remove m n

  ∂-list-equiv : ∂• List ⧟ (List ⊗ List)
  ∂-list-equiv = forget-isolated-pos ⋆ₑ Equiv.inv glue-at-hole
```

### As a fixpoint { #list-as-fixpoint }

Instead of giving lists directly in terms of length and positions,
we can show that they are the (unique) solution to the fixpoint problem \( Y = 1 + X \times Y \).
Let's define a two-parameter container \( \mathsf{L} = (S \lhd X, Y) \) and show that \( \mu \mathsf{L} \) is equivalent to \( \mathsf{List} \).
```agda
private
  data S : Type where
    nil cons : S

  X : S → Type
  X nil = 𝟘
  X cons = 𝟙

  Y : S → Type
  Y nil = 𝟘
  Y cons = 𝟙

  pattern x = ₀
  pattern y = ₁

L : Container ℓ-zero 𝟚
L .Shape = S
L .Pos x = X
L .Pos y = Y
```

The construction proceeds by observing that shapes of \( \mu \mathsf{L} \) are trees
with at most one branch, hence equivalent to \( ℕ \).
```agda
μL⧟List : μ L ⧟ List
μL⧟List = [ depth-equiv ◁≃ path-equiv ]  where
```

Shapes are trees \( \mathsf{W}(S, Y) \).
We compute their depth by induction.
```agda
  _ : μ L .Shape ≡ W S Y
  _ = refl

  depth : W S Y → ℕ
  depth = W-rec λ where
    (nil , _) → 0
    (cons , n) → suc (n •)
```

The positions \( Y \) force the tree to branch at most once,
consequently there is a unique tree for each depth.
This defines the equivalence of shapes.
```agda
  depth-equiv : W S Y ≃ ℕ
  depth-equiv = isoToEquiv λ where
    .Iso.fun → depth
    .Iso.inv → Nat.elim (sup nil (λ ())) λ n w → sup cons λ _ → w
    .Iso.rightInv → Nat.elim refl λ n → cong suc
    .Iso.leftInv → W-elim λ where
      nil f ind → cong (sup nil) $ funExt λ ()
      cons f ind → cong (sup cons) $ funExt ind

  unique-tree-of-depth : ∀ n → ∃![ x ∈ W S Y ] depth x ≡ n
  unique-tree-of-depth = equivIsEquiv depth-equiv .equiv-proof
```

By induction, it is straightforward to show that there are exactly
\( n \) paths into such a tree of depth \( n \).
This is the desired equivalence of positions.
```agda
  path-equiv : 𝟙 → (x : W S Y) → [ depth x ] ≃ Wᴰ S Y X x
  path-equiv _ = W-elim λ where
    nil f _ → Empty.uninhabEquiv (λ ()) λ where
      (top p) → 𝟘-rec p
      (below p q) → 𝟘-rec p
    cons f ind-≃ →
      𝟙 ⊎ [ depth (f •) ]
        ≃⟨ ⊎-right-≃ $ ind-≃ • ⟩
      𝟙 ⊎ (Wᴰ S Y X (f •))
        ≃⟨ ⊎-right-≃ $ invEquiv $ Sigma.Σ-contractFst isContr-𝟙* ⟩
      𝟙 ⊎ (Σ[ p ∈ 𝟙 ] Wᴰ S Y X (f p))
        ≃⟨ Wᴰ-in-equiv _ _ _ cons f ⟩
      Wᴰ S Y X (sup cons f)
        ≃∎
```
