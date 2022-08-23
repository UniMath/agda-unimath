---
title: Decidable subtypes of finite types
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.decidable-subtypes where

open import foundation.decidable-subtypes public

open import elementary-number-theory.inequality-natural-numbers

open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
```

## Properties

### The type of decidable subtypes of a finite type is finite

```agda
is-finite-decidable-subtype-is-finite :
  {l1 l2 : Level} {X : UU l1} →
  is-finite X → is-finite (decidable-subtype l2 X)
is-finite-decidable-subtype-is-finite H =
  is-finite-function-type H is-finite-decidable-Prop

subtype-𝔽 :
  {l1 : Level} (l2 : Level) → 𝔽 l1 → 𝔽 (l1 ⊔ lsuc l2)
pr1 (subtype-𝔽 l2 X) = decidable-subtype l2 (type-𝔽 X)
pr2 (subtype-𝔽 l2 X) =
  is-finite-decidable-subtype-is-finite (is-finite-type-𝔽 X)

has-decidable-equality-subtype-𝔽 :
  {l1 l2 : Level} (X : 𝔽 l1) →
  has-decidable-equality (decidable-subtype l2 (type-𝔽 X))
has-decidable-equality-subtype-𝔽 {l1} {l2} X =
  has-decidable-equality-is-finite
    ( is-finite-decidable-subtype-is-finite (is-finite-type-𝔽 X))
```

### Decidable subtypes of finite types are finite

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X)
  where

  abstract
    is-finite-type-decidable-subtype :
      is-finite X → is-finite (type-decidable-subtype P)
    is-finite-type-decidable-subtype H =
      is-finite-Σ H
        ( λ x →
          is-finite-is-decidable-Prop
            ( prop-decidable-Prop (P x))
            ( is-decidable-type-decidable-Prop (P x)))
```

### The underlying type of a decidable subtype has decidable equality

```agda
has-decidable-equality-type-decidable-subtype-is-finite :
  {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X) → is-finite X →
  has-decidable-equality (type-decidable-subtype P)
has-decidable-equality-type-decidable-subtype-is-finite P H =
  has-decidable-equality-is-finite (is-finite-type-decidable-subtype P H)
```

### The number of elements of a decidable subtype of a finite type is smaller than the number of elements of the ambient type

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X)
  where

  leq-number-of-elements-type-decidable-subtype :
    (H : is-finite X) →
    leq-ℕ
      ( number-of-elements-is-finite (is-finite-type-decidable-subtype P H))
      ( number-of-elements-is-finite H)
  leq-number-of-elements-type-decidable-subtype H = {!!}
