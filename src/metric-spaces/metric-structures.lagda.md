# Metric structures

```agda
module metric-spaces.metric-structures where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.closed-premetric-structures
open import metric-spaces.ordering-premetric-structures
open import metric-spaces.premetric-structures
```

</details>

## Idea

A [premetric structure](metric-spaces.metric-structures.md) is a
{{#concept "metric" Disambiguation="premetric structure" Agda=is-metric-Premetric}}
if it is reflexive, symmetric, local, and triangular.

## Definitions

### The property of being a metric premetric structure

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-metric-prop-Premetric : Prop (l1 ⊔ l2)
  is-metric-prop-Premetric =
    product-Prop
      ( is-reflexive-prop-Premetric B)
      ( product-Prop
        ( is-symmetric-prop-Premetric B)
        ( product-Prop
          ( is-local-prop-Premetric B)
          ( is-triangular-prop-Premetric B)))

  is-metric-Premetric : UU (l1 ⊔ l2)
  is-metric-Premetric = type-Prop is-metric-prop-Premetric

  is-prop-is-metric-Premetric : is-prop is-metric-Premetric
  is-prop-is-metric-Premetric =
    is-prop-type-Prop is-metric-prop-Premetric
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (M : is-metric-Premetric B)
  where

  is-reflexive-is-metric-Premetric : is-reflexive-Premetric B
  is-reflexive-is-metric-Premetric = pr1 M

  is-symmetric-is-metric-Premetric : is-symmetric-Premetric B
  is-symmetric-is-metric-Premetric = pr1 (pr2 M)

  is-local-is-metric-Premetric : is-local-Premetric B
  is-local-is-metric-Premetric = pr1 (pr2 (pr2 M))

  is-triangular-is-metric-Premetric : is-triangular-Premetric B
  is-triangular-is-metric-Premetric = pr2 (pr2 (pr2 M))

  is-monotonic-is-metric-Premetric : is-monotonic-Premetric B
  is-monotonic-is-metric-Premetric =
    is-monotonic-is-reflexive-triangular-Premetric
      B
      is-reflexive-is-metric-Premetric
      is-triangular-is-metric-Premetric
```

## Properties

### The closure of a metric structure is metric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (M : is-metric-Premetric B)
  where

  preserves-is-metric-closure-Premetric :
    is-metric-Premetric (closure-Premetric B)
  preserves-is-metric-closure-Premetric =
    ( is-reflexive-closure-Premetric
      ( B)
      ( is-reflexive-is-metric-Premetric B M)) ,
    ( is-symmetric-closure-Premetric
      ( B)
      ( is-symmetric-is-metric-Premetric B M)) ,
    ( is-local-closure-Premetric
      ( B)
      ( is-local-is-metric-Premetric B M)) ,
    ( is-triangular-closure-Premetric
      ( B)
      ( is-triangular-is-metric-Premetric B M))
```

### The closure of a metric structure is the finest closed metric coarser than it

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (M : is-metric-Premetric B)
  where

  leq-closure-is-metric-Premetric : leq-Premetric B (closure-Premetric B)
  leq-closure-is-metric-Premetric =
    leq-closure-monotonic-Premetric
      ( B)
      ( is-monotonic-is-metric-Premetric B M)

  leq-closure-closed-is-metric-Premetric :
    (B' : Premetric l2 A) →
    is-metric-Premetric B' →
    is-closed-Premetric B' →
    leq-Premetric B B' →
    leq-Premetric (closure-Premetric B) B'
  leq-closure-closed-is-metric-Premetric B' =
    leq-closure-leq-closed-monotonic-Premetric B B' ∘
    is-monotonic-is-metric-Premetric B'
```
