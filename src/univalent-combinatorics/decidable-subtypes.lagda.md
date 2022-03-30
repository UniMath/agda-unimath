---
title: Decidable subtypes of finite types
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.decidable-subtypes where

open import foundation.decidable-subtypes public

open import elementary-number-theory.inequality-natural-numbers using (leq-ℕ)

open import foundation.decidable-propositions using
  ( prop-decidable-Prop; is-decidable-type-decidable-Prop)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.dependent-sum-finite-types using
  ( is-finite-Σ)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-is-decidable-Prop; number-of-elements-is-finite)
```

## Properties

### Decidable subtypes of finite types are finite

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X)
  where

  abstract
    is-finite-decidable-subtype :
      is-finite X → is-finite (type-decidable-subtype P)
    is-finite-decidable-subtype H =
      is-finite-Σ H
        ( λ x →
          is-finite-is-decidable-Prop
            ( prop-decidable-Prop (P x))
            ( is-decidable-type-decidable-Prop (P x)))
```

### The number of elements of a decidable subtype of a finite type is smaller than the number of elements of the ambient type

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X)
  where

  leq-number-of-elements-type-decidable-subtype :
    (H : is-finite X) →
    leq-ℕ
      ( number-of-elements-is-finite (is-finite-decidable-subtype P H))
      ( number-of-elements-is-finite H)
  leq-number-of-elements-type-decidable-subtype H = {!!}
