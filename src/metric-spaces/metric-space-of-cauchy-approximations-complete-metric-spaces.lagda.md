# The metric space of Cauchy approximations in a complete metric space

```agda
module metric-spaces.metric-space-of-cauchy-approximations-complete-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-space-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-space-of-convergent-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

The type of
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
a [complete metric space](metric-spaces.complete-metric-spaces.md) `A` inherits
the
[metric structure](metric-spaces.metric-space-of-cauchy-approximations-metric-spaces.md)
of the Cauchy approximations in the underlying metric space; this is the
{{#concept "metric space of Cauchy approximations" Disambiguation="in a complete metric space" Agda=metric-space-of-cauchy-approximations-Complete-Metric-Space}}
in a complete metric space.

All Cauchy approximations in a complete metric space are
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md)
and the corresponding map into the
[metric space of convergent Cauchy approximations](metric-spaces.metric-space-of-convergent-cauchy-approximations-metric-spaces.md)
is an [isometry](metric-spaces.isometries-metric-spaces.md).

## Definitions

### The metric space of Cauchy approximations in a complete metric space

```agda
module _
  {l1 l2 : Level} (A : Complete-Metric-Space l1 l2)
  where

  metric-space-of-cauchy-approximations-Complete-Metric-Space :
    Metric-Space (l1 ⊔ l2) l2
  metric-space-of-cauchy-approximations-Complete-Metric-Space =
    metric-space-of-cauchy-approximations-Metric-Space
      ( metric-space-Complete-Metric-Space A)
```

## Properties

### The map from a Cauchy approximation in a metric space to its convergent approximation is an isometry

```agda
module _
  {l1 l2 : Level} (A : Complete-Metric-Space l1 l2)
  where

  is-isometry-convergent-cauchy-approximation-Complete-Metric-Space :
    is-isometry-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( convergent-cauchy-approximation-Complete-Metric-Space A)
  is-isometry-convergent-cauchy-approximation-Complete-Metric-Space d x y =
    (id , id)

  isometry-convergent-cauchy-approximation-Complete-Metric-Space :
    isometry-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
  isometry-convergent-cauchy-approximation-Complete-Metric-Space =
    convergent-cauchy-approximation-Complete-Metric-Space A ,
    is-isometry-convergent-cauchy-approximation-Complete-Metric-Space
```

### The metric space of Cauchy approximations in a complete metric space is equal to the metric space of convergent Cauchy approximations in its underlying metric space

```agda
module _
  {l1 l2 : Level} (A : Complete-Metric-Space l1 l2)
  where

  eq-metric-space-convergent-cauchy-approximations-Complete-Metric-Space :
    ( metric-space-of-cauchy-approximations-Complete-Metric-Space A) ＝
    ( metric-space-of-convergent-cauchy-approximations-Metric-Space
      ( metric-space-Complete-Metric-Space A))
  eq-metric-space-convergent-cauchy-approximations-Complete-Metric-Space =
    eq-isometric-equiv-Metric-Space'
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( convergent-cauchy-approximation-Complete-Metric-Space A ,
        is-equiv-convergent-cauchy-approximation-Complete-Metric-Space A ,
        is-isometry-convergent-cauchy-approximation-Complete-Metric-Space A)
```

### The map from a Cauchy approximation in a metric space to its convergent approximation is short

```agda
module _
  {l1 l2 : Level} (A : Complete-Metric-Space l1 l2)
  where

  short-convergent-cauchy-approximation-Complete-Metric-Space :
    short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
  short-convergent-cauchy-approximation-Complete-Metric-Space =
    short-isometry-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( isometry-convergent-cauchy-approximation-Complete-Metric-Space A)

  is-short-convergent-cauchy-approximation-Complete-Metric-Space :
    is-short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( convergent-cauchy-approximation-Complete-Metric-Space A)
  is-short-convergent-cauchy-approximation-Complete-Metric-Space =
    is-short-map-short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( short-convergent-cauchy-approximation-Complete-Metric-Space)
```

### The map from a Cauchy approximation in a complete metric space to its limit is short

```agda
module _
  {l1 l2 : Level} (A : Complete-Metric-Space l1 l2)
  where

  short-limit-cauchy-approximation-Complete-Metric-Space :
    short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-Complete-Metric-Space A)
  short-limit-cauchy-approximation-Complete-Metric-Space =
    comp-short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( metric-space-Complete-Metric-Space A)
      ( short-limit-convergent-cauchy-approximation-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( short-convergent-cauchy-approximation-Complete-Metric-Space A)

  is-short-limit-cauchy-approximation-Complete-Metric-Space :
    is-short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-Complete-Metric-Space A)
      ( limit-cauchy-approximation-Complete-Metric-Space A)
  is-short-limit-cauchy-approximation-Complete-Metric-Space =
    is-short-map-short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-Complete-Metric-Space A)
      ( short-limit-cauchy-approximation-Complete-Metric-Space)
```

### The metric space of Cauchy approximations in a complete metric space is complete

Given a Cauchy approximation of Cauchy approximations `U : ℚ⁺ → ℚ⁺ → A` in a
complete metric space `A`, we construct its limit as follows:

1. for any `η : ℚ⁺`, the partial application `ε ↦ U ε η` is a Cauchy
   approximation in `A`;
2. since `A` is complete, it converges to some `lim-η : A`;
3. the assignment `η ↦ lim-η` is a Cauchy approximation in `A`;
4. by construction it's a limit of `U` in the space of Cauchy approximations.

```agda
module _
  {l1 l2 : Level} (A : Complete-Metric-Space l1 l2)
  (U : cauchy-approximation-Metric-Space
    ( metric-space-of-cauchy-approximations-Complete-Metric-Space A))
  where

  map-lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space :
    ℚ⁺ → type-Complete-Metric-Space A
  map-lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space
    η =
    limit-cauchy-approximation-Complete-Metric-Space
      ( A)
      ( map-swap-cauchy-approximation-Metric-Space
        ( metric-space-Complete-Metric-Space A)
        ( U)
        ( η))

  is-cauchy-map-lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space :
    is-cauchy-approximation-Metric-Space
      ( metric-space-Complete-Metric-Space A)
      ( map-lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space)
  is-cauchy-map-lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space
    ε δ =
    is-short-limit-cauchy-approximation-Complete-Metric-Space
      ( A)
      ( ε +ℚ⁺ δ)
      ( map-swap-cauchy-approximation-Metric-Space
        ( metric-space-Complete-Metric-Space A)
        ( U)
        ( ε))
      ( map-swap-cauchy-approximation-Metric-Space
        ( metric-space-Complete-Metric-Space A)
        ( U)
        ( δ))
      ( λ η →
        is-cauchy-approximation-map-cauchy-approximation-Metric-Space
          ( metric-space-Complete-Metric-Space A)
          ( map-cauchy-approximation-Metric-Space
            ( metric-space-of-cauchy-approximations-Complete-Metric-Space
              ( A))
            ( U)
            ( η))
          ( ε)
          ( δ))

  lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space :
    cauchy-approximation-Metric-Space
      (metric-space-Complete-Metric-Space A)
  lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space
    =
    map-lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space ,
    is-cauchy-map-lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space

  is-limit-lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space
        ( A))
      ( U)
      ( lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space)
  is-limit-lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space
    ε δ η =
    is-limit-limit-cauchy-approximation-Complete-Metric-Space
      ( A)
      ( map-swap-cauchy-approximation-Metric-Space
        ( metric-space-Complete-Metric-Space A)
        ( U)
        ( η))
      ( ε)
      ( δ)

module _
  {l1 l2 : Level} (A : Complete-Metric-Space l1 l2)
  where

  is-complete-metric-space-of-cauchy-approximations-Complete-Metric-Space :
    is-complete-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
  is-complete-metric-space-of-cauchy-approximations-Complete-Metric-Space U =
    ( lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space
      ( A)
      ( U)) ,
    ( is-limit-lim-cauchy-approximation-cauchy-approximations-Complete-Metric-Space
      ( A)
      ( U))
```

### The complete metric space of Cauchy approximations in a complete metric space

```agda
module _
  {l1 l2 : Level} (A : Complete-Metric-Space l1 l2)
  where

  complete-metric-space-of-cauchy-approximations-Complete-Metric-Space :
    Complete-Metric-Space (l1 ⊔ l2) l2
  complete-metric-space-of-cauchy-approximations-Complete-Metric-Space =
    ( metric-space-of-cauchy-approximations-Complete-Metric-Space A) ,
    ( is-complete-metric-space-of-cauchy-approximations-Complete-Metric-Space A)
```

### A metric space is complete if and only if its metric space of Cauchy approximations is complete

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-complete-is-complete-metric-space-of-cauchy-approximations-Metric-Space :
    is-complete-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space A) →
    is-complete-Metric-Space A
  is-complete-is-complete-metric-space-of-cauchy-approximations-Metric-Space
    H f =
    rec-trunc-Prop
      ( is-convergent-prop-cauchy-approximation-Metric-Space A f)
      ( λ d →
        ( map-cauchy-approximation-Metric-Space A lim-const-map-f d) ,
        ( is-lim-f-lim-const-map-f d))
      ( is-inhabited-ℚ⁺)
    where

    const-map-f :
      ℚ⁺ → cauchy-approximation-Metric-Space A
    const-map-f =
      ( const-cauchy-approximation-Metric-Space A) ∘
      ( map-cauchy-approximation-Metric-Space A f)

    is-cauchy-const-map-f :
      is-cauchy-approximation-Metric-Space
        ( metric-space-of-cauchy-approximations-Metric-Space A)
        ( const-map-f)
    is-cauchy-const-map-f ε δ d =
      is-cauchy-approximation-map-cauchy-approximation-Metric-Space
        ( A)
        ( f)
        ( ε)
        ( δ)

    lim-const-map-f :
      cauchy-approximation-Metric-Space A
    lim-const-map-f =
      limit-cauchy-approximation-Complete-Metric-Space
        ( metric-space-of-cauchy-approximations-Metric-Space A , H)
        ( const-map-f , is-cauchy-const-map-f)

    is-lim-f-lim-const-map-f :
      (d : ℚ⁺) →
      is-limit-cauchy-approximation-Metric-Space
        ( A)
        ( f)
        ( map-cauchy-approximation-Metric-Space A lim-const-map-f d)
    is-lim-f-lim-const-map-f d ε δ =
      is-limit-limit-cauchy-approximation-Complete-Metric-Space
        ( metric-space-of-cauchy-approximations-Metric-Space A , H)
        ( const-map-f , is-cauchy-const-map-f)
        ( ε)
        ( δ)
        ( d)

  iff-is-complete-is-complete-metric-space-of-cauchy-approximations-Metric-Space :
    is-complete-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space A) ↔
    is-complete-Metric-Space A
  iff-is-complete-is-complete-metric-space-of-cauchy-approximations-Metric-Space
    =
    ( is-complete-is-complete-metric-space-of-cauchy-approximations-Metric-Space) ,
    ( is-complete-metric-space-of-cauchy-approximations-Complete-Metric-Space ∘
      pair A)
```
