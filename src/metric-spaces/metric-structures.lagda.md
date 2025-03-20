# Metric structures

```agda
open import foundation.function-extensionality-axiom

module
  metric-spaces.metric-structures
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types funext
open import foundation.logical-equivalences funext
open import foundation.propositions funext
open import foundation.universe-levels

open import metric-spaces.closed-premetric-structures funext
open import metric-spaces.extensional-premetric-structures funext
open import metric-spaces.monotonic-premetric-structures funext
open import metric-spaces.ordering-premetric-structures funext
open import metric-spaces.premetric-structures funext
open import metric-spaces.pseudometric-structures funext
open import metric-spaces.reflexive-premetric-structures funext
open import metric-spaces.symmetric-premetric-structures funext
open import metric-spaces.triangular-premetric-structures funext
```

</details>

## Idea

A [premetric structure](metric-spaces.metric-structures.md) is a
{{#concept "metric" Disambiguation="structure on a type" Agda=is-metric-Premetric}}
if it is an [extensional](metric-spaces.extensional-premetric-structures.md)
[pseudometric](metric-spaces.pseudometric-spaces.md). I.e., if the neighborhood
relation is [reflexive](metric-spaces.reflexive-premetric-structures.md),
[symmetric](metric-spaces.symmetric-premetric-structures.md),
[triangular](metric-spaces.triangular-premetric-structures.md), and
[local](metric-spaces.extensional-premetric-structures.md).

## Definitions

### The property of being a metric premetric structure

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-metric-prop-Premetric : Prop (l1 ⊔ l2)
  is-metric-prop-Premetric =
    product-Prop
      ( is-pseudometric-prop-Premetric B)
      ( is-local-prop-Premetric B)

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

  is-pseudometric-is-metric-Premetric : is-pseudometric-Premetric B
  is-pseudometric-is-metric-Premetric = pr1 M

  is-reflexive-is-metric-Premetric : is-reflexive-Premetric B
  is-reflexive-is-metric-Premetric =
    is-reflexive-is-pseudometric-Premetric
      B
      is-pseudometric-is-metric-Premetric

  is-symmetric-is-metric-Premetric : is-symmetric-Premetric B
  is-symmetric-is-metric-Premetric =
    is-symmetric-is-pseudometric-Premetric
      B
      is-pseudometric-is-metric-Premetric

  is-triangular-is-metric-Premetric : is-triangular-Premetric B
  is-triangular-is-metric-Premetric =
    is-triangular-is-pseudometric-Premetric
      B
      is-pseudometric-is-metric-Premetric

  is-local-is-metric-Premetric : is-local-Premetric B
  is-local-is-metric-Premetric = pr2 M

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
    ( preserves-is-pseudometric-closure-Premetric
      ( B)
      ( is-pseudometric-is-metric-Premetric B M)) ,
    ( is-local-closure-Premetric
      ( B)
      ( is-local-is-metric-Premetric B M))
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
