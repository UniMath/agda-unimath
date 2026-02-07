# The Cauchy pseudocompletion of a metric space

```agda
module metric-spaces.cauchy-pseudocompletions-of-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-in-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

The
{{#concept "Cauchy pseudocompletion" Disambiguation="of a metric space" Agda=cauchy-pseudocompletion-Metric-Space}}
of a [metric space](metric-spaces.metric-spaces.md) `M` is the
[Cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces.md)
of its underlying [pseudometric space](metric-spaces.pseudometric-spaces.md):
the pseudometric space of
[Cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
in `M` where two Cauchy approximations `x` and `y` are in a
[`d`-neighborhood](metric-spaces.rational-neighborhood-relations.md) of one
another if for all `δ ε : ℚ⁺`, `x δ` and `y ε` are in a
`(δ + ε + d)`-neighborhood of one another in `M`.

Any Cauchy approximation in the Cauchy pseudocompletion has a
[limit](metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.md).
If the metric space is [complete](metric-spaces.complete-metric-spaces.md), it
is a [retract](foundation.retracts-of-types.md) of its Cauchy pseudocompletion.

## Definition

### The Cauchy pseudocompletion of a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  cauchy-pseudocompletion-Metric-Space :
    Pseudometric-Space (l1 ⊔ l2) l2
  cauchy-pseudocompletion-Metric-Space =
    cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
```

### The Cauchy pseudocompletion neighborhood relation on the type of Cauchy approximations in a pseudometric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  neighborhood-prop-cauchy-pseudocompletion-Metric-Space :
    Rational-Neighborhood-Relation l2
      (cauchy-approximation-Metric-Space M)
  neighborhood-prop-cauchy-pseudocompletion-Metric-Space =
    neighborhood-prop-cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)

  neighborhood-cauchy-pseudocompletion-Metric-Space :
    ℚ⁺ → Relation l2 (cauchy-approximation-Metric-Space M)
  neighborhood-cauchy-pseudocompletion-Metric-Space =
    neighborhood-cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
```

## Properties

### The neighborhood relation is reflexive

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  abstract
    is-reflexive-neighborhood-cauchy-pseudocompletion-Metric-Space :
      (d : ℚ⁺) (x : cauchy-approximation-Metric-Space M) →
      neighborhood-cauchy-pseudocompletion-Metric-Space M d x x
    is-reflexive-neighborhood-cauchy-pseudocompletion-Metric-Space =
      is-reflexive-neighborhood-cauchy-pseudocompletion-Pseudometric-Space
        ( pseudometric-Metric-Space M)
```

### The neighborhood relation is symmetric

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

    abstract
      is-symmetric-neighborhood-cauchy-pseudocompletion-Metric-Space :
        (d : ℚ⁺) (x y : cauchy-approximation-Metric-Space M) →
        neighborhood-cauchy-pseudocompletion-Metric-Space M d x y →
        neighborhood-cauchy-pseudocompletion-Metric-Space M d y x
      is-symmetric-neighborhood-cauchy-pseudocompletion-Metric-Space =
        is-symmetric-neighborhood-cauchy-pseudocompletion-Pseudometric-Space
          ( pseudometric-Metric-Space M)
```

### The neighborhood relation is triangular

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  abstract
    is-triangular-neighborhood-cauchy-pseudocompletion-Metric-Space :
      (x y z : cauchy-approximation-Metric-Space M) →
      (dxy dyz : ℚ⁺) →
      neighborhood-cauchy-pseudocompletion-Metric-Space M dyz y z →
      neighborhood-cauchy-pseudocompletion-Metric-Space M dxy x y →
      neighborhood-cauchy-pseudocompletion-Metric-Space
        ( M)
        ( dxy +ℚ⁺ dyz)
        ( x)
        ( z)
    is-triangular-neighborhood-cauchy-pseudocompletion-Metric-Space =
      is-triangular-neighborhood-cauchy-pseudocompletion-Pseudometric-Space
        ( pseudometric-Metric-Space M)
```

### The neighborhood relation is saturated

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  abstract
    is-saturated-neighborhood-cauchy-pseudocompletion-Metric-Space :
      ( ε : ℚ⁺) (x y : cauchy-approximation-Metric-Space M) →
      ( (δ : ℚ⁺) →
        neighborhood-cauchy-pseudocompletion-Metric-Space
          ( M)
          ( ε +ℚ⁺ δ)
          ( x)
          ( y)) →
      neighborhood-cauchy-pseudocompletion-Metric-Space M ε x y
    is-saturated-neighborhood-cauchy-pseudocompletion-Metric-Space =
      is-saturated-neighborhood-cauchy-pseudocompletion-Pseudometric-Space
        ( pseudometric-Metric-Space M)
```

### The isometry from a metric space to its Cauchy pseudocompletion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  isometry-unit-cauchy-pseudocompletion-Metric-Space :
    isometry-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( cauchy-pseudocompletion-Metric-Space M)
  isometry-unit-cauchy-pseudocompletion-Metric-Space =
    isometry-unit-cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)

  map-unit-cauchy-pseudocompletion-Metric-Space :
    type-Metric-Space M → cauchy-approximation-Metric-Space M
  map-unit-cauchy-pseudocompletion-Metric-Space =
    map-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( cauchy-pseudocompletion-Metric-Space M)
      ( isometry-unit-cauchy-pseudocompletion-Metric-Space)

  abstract
    is-isometry-map-unit-cauchy-pseudocompletion-Metric-Space :
      is-isometry-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( cauchy-pseudocompletion-Metric-Space M)
        ( map-unit-cauchy-pseudocompletion-Metric-Space)
    is-isometry-map-unit-cauchy-pseudocompletion-Metric-Space =
      is-isometry-map-isometry-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( cauchy-pseudocompletion-Metric-Space M)
        ( isometry-unit-cauchy-pseudocompletion-Metric-Space)
```

### Any Cauchy approximation in the Cauchy pseudocompletion of a metric space has a limit

```agda
module _
  { l1 l2 : Level} (M : Metric-Space l1 l2)
  ( U :
    cauchy-approximation-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M))
  where

  has-limit-cauchy-approximation-cauchy-pseudocompletion-Metric-Space :
    Σ ( cauchy-approximation-Metric-Space M)
      ( is-limit-cauchy-approximation-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( U))
  has-limit-cauchy-approximation-cauchy-pseudocompletion-Metric-Space =
    has-limit-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( U)

  lim-cauchy-approximation-cauchy-pseudocompletion-Metric-Space :
    cauchy-approximation-Metric-Space M
  lim-cauchy-approximation-cauchy-pseudocompletion-Metric-Space =
    pr1 has-limit-cauchy-approximation-cauchy-pseudocompletion-Metric-Space

  is-limit-lim-cauchy-approximation-cauchy-pseudocompletion-Metric-Space :
    is-limit-cauchy-approximation-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( U)
      ( lim-cauchy-approximation-cauchy-pseudocompletion-Metric-Space)
  is-limit-lim-cauchy-approximation-cauchy-pseudocompletion-Metric-Space =
    pr2 has-limit-cauchy-approximation-cauchy-pseudocompletion-Metric-Space
```

### The isometry from a Cauchy approximation in the Cauchy pseudocompletion to its limit

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  isometry-lim-cauchy-approximation-cauchy-pseudocompletion-Metric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M))
      ( cauchy-pseudocompletion-Metric-Space M)
  isometry-lim-cauchy-approximation-cauchy-pseudocompletion-Metric-Space =
    isometry-lim-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
```
