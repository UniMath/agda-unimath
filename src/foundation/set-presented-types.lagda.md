# Set presented types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.set-presented-types where

open import foundation.equivalences using (is-equiv)
open import foundation.existential-quantification using (∃-Prop)
open import foundation.functions using (_∘_)
open import foundation.propositions using (UU-Prop)
open import foundation.set-truncations using (unit-trunc-Set)
open import foundation.sets using (UU-Set; type-Set)
open import foundation.universe-levels using (UU; Level; _⊔_)
```

## Idea

A type `A` is said to be set presented if there exists a map `f : X → A` from a set `X` such that the composite `X → A → type-trunc-Set A` is an equivalence.

```agda
has-set-presentation-Prop :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU l2) → UU-Prop (l1 ⊔ l2)
has-set-presentation-Prop A B =
  ∃-Prop (type-Set A → B) (λ f → is-equiv (unit-trunc-Set ∘ f))
```
