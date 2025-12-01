# Limits of Cauchy approximations in metric spaces

```agda
module metric-spaces.limits-of-cauchy-approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.action-of-short-maps-on-cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

A [Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md)
`f : ℚ⁺ → A` in a [metric space](metric-spaces.metric-spaces.md) `A` has a
{{#concept "limit" Disambiguation="of a Cauchy approximation in a metric space" Agda=is-limit-cauchy-approximation-Metric-Space}}
`x : A` if `f ε` is near `x` for small `ε : ℚ⁺`. More precisely, `f` has a limit
if `f ε` is in a
`ε + δ`-[neighborhood](metric-spaces.rational-neighborhood-relations.md) of `x`
for all
[positive rationals](elementary-number-theory.positive-rational-numbers.md) `ε`
and `δ`.

These are
[limits](metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.md)
in the underlying [pseudometric space](metric-spaces.pseudometric-spaces.md)
but, because metric spaces are
[extensional](metric-spaces.extensionality-pseudometric-spaces.md), all limits
of a Cauchy approximation in a metric space are equal.

## Definitions

### The property of having a limit in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space A)
  where

  is-limit-cauchy-approximation-prop-Metric-Space :
    type-Metric-Space A → Prop l2
  is-limit-cauchy-approximation-prop-Metric-Space =
    is-limit-cauchy-approximation-prop-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( f)

  is-limit-cauchy-approximation-Metric-Space :
    type-Metric-Space A → UU l2
  is-limit-cauchy-approximation-Metric-Space =
    type-Prop ∘ is-limit-cauchy-approximation-prop-Metric-Space
```

## Properties

### Saturation of the limit

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space A)
  (x : type-Metric-Space A)
  where

  abstract
    saturated-is-limit-cauchy-approximation-Metric-Space :
      is-limit-cauchy-approximation-Metric-Space A f x →
      (ε : ℚ⁺) →
      neighborhood-Metric-Space A ε
        ( map-cauchy-approximation-Metric-Space A f ε)
        ( x)
    saturated-is-limit-cauchy-approximation-Metric-Space =
      saturated-is-limit-cauchy-approximation-Pseudometric-Space
        ( pseudometric-Metric-Space A)
        ( f)
        ( x)
```

### Limits in a metric space are unique

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space A)
  (x y : type-Metric-Space A)
  where

  all-sim-is-limit-cauchy-approximation-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space A f x →
    is-limit-cauchy-approximation-Metric-Space A f y →
    sim-Metric-Space A x y
  all-sim-is-limit-cauchy-approximation-Metric-Space =
    all-sim-is-limit-cauchy-approximation-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( f)
      ( x)
      ( y)

  all-eq-is-limit-cauchy-approximation-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space A f x →
    is-limit-cauchy-approximation-Metric-Space A f y →
    x ＝ y
  all-eq-is-limit-cauchy-approximation-Metric-Space lim-x lim-y =
    eq-sim-Metric-Space
      ( A)
      ( x)
      ( y)
      ( all-sim-is-limit-cauchy-approximation-Metric-Space lim-x lim-y)
```

### The value of a constant Cauchy approximation is its limit

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (x : type-Metric-Space A)
  where

  is-limit-const-cauchy-approximation-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( A)
      ( const-cauchy-approximation-Metric-Space A x)
      ( x)
  is-limit-const-cauchy-approximation-Metric-Space =
    is-limit-const-cauchy-approximation-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( x)
```

### The action of short maps on Cauchy approximations preserves limits

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-function-Metric-Space A B)
  (a : cauchy-approximation-Metric-Space A)
  (lim : type-Metric-Space A)
  where

  abstract
    preserves-limit-cauchy-approximation-map-short-function-Metric-Space :
      is-limit-cauchy-approximation-Metric-Space A a lim →
      is-limit-cauchy-approximation-Metric-Space
        ( B)
        ( map-short-function-cauchy-approximation-Metric-Space A B f a)
        ( map-short-function-Metric-Space A B f lim)
    preserves-limit-cauchy-approximation-map-short-function-Metric-Space
      is-lim-a ε δ =
      is-short-map-short-function-Metric-Space A B
        ( f)
        ( ε +ℚ⁺ δ)
        ( map-cauchy-approximation-Metric-Space A a ε)
        ( lim)
        ( is-lim-a ε δ)
```

## See also

- [Convergent cauchy approximations](metric-spaces.convergent-cauchy-approximations-metric-spaces.md)
  are Cauchy approximations with a limit.

## References

Our definition of limit of Cauchy approximation follows Definition 11.2.10 of
{{#cite UF13}}.

{{#bibliography}}
