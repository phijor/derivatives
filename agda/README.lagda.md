<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
module README where

open import Derivative.Prelude
open import Derivative.Basics.Decidable
open import Derivative.Basics.Equiv

private
  variable
    ℓ : Level
    A B : Type ℓ
    a : A
```
-->

# Removing Isolated Points in Univalent Foundations

```agda
open import Derivative.Isolated
```

Definition 2.1: Isolated points.
```agda
_ : (a : A) → Type _
_ = isIsolated
```

Lemma 2.2: Isolated points have propositional paths.
```agda
_ : (a : A) → isIsolated a → (b : A) → isProp (a ≡ b)
_ = isIsolated→isPropPath
```

Corollary 2.3: Being isolated is a proposition.
```agda
_ : (a : A) → isProp (isIsolated a)
_ = isPropIsIsolated
```

Proposition 2.4: Isolated points form a set.
```agda
Proposition-2-4 : isSet (A °)
Proposition-2-4 = isSetIsolated
```

Lemma 2.5: Equivalences preserve and reflect isolated points, hence induce an equivalence.
```agda
Lemma-2-5 : (e : A ≃ B) → A ° ≃ B °
Lemma-2-5 = IsolatedSubstEquiv
```

# Derivatives of Containers

```agda
import Derivative.Container
```

## Derivatives, Universally

```agda
import Derivative.Adjunction
```

## Basic Laws of Derivatives

```agda
import Derivative.Properties
```

# The Chain Rule

```agda
import Derivative.ChainRule
```

# Derivatives of Fixed Points

```agda
import Derivative.Indexed.ChainRule
import Derivative.Indexed.Mu
import Derivative.Indexed.MuRule
```
