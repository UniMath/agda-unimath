# Limits of Cauchy approximations in metric spaces

```agda
module metric-spaces.limits-of-cauchy-approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A [Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md)
`f : ℚ⁺ → A` in a [metric space](metric-spaces.metric-spaces.md) `A` has a
{{#concept "limit" Disambiguation="of a Cauchy approximation in a metric space Agda=is-limit-cauchy-approximation-Metric-Space}}
`x : A` if `f ε` is near `x` for small `ε : ℚ⁺`; more precisely, if `f ε` is in
a `ε + δ`-[neighborhood](metric-spaces.rational-neighborhoods.md) of `x` for all
`ε δ : ℚ⁺`.

## Definitions

### The property of having a limit in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space A)
  where

  is-limit-cauchy-approximation-prop-Metric-Space :
    type-Metric-Space A → Prop l2
  is-limit-cauchy-approximation-prop-Metric-Space lim =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        neighborhood-prop-Metric-Space
          ( A)
          ( ε)
          ( map-cauchy-approximation-Metric-Space A f ε)
          ( lim))

  is-limit-cauchy-approximation-Metric-Space :
    type-Metric-Space A → UU l2
  is-limit-cauchy-approximation-Metric-Space =
    type-Prop ∘ is-limit-cauchy-approximation-prop-Metric-Space
```

## Properties

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
  all-sim-is-limit-cauchy-approximation-Metric-Space lim-x lim-y δ =
    let
      (ε , ε+ε<δ) = bound-double-le-ℚ⁺ δ
      fε = map-cauchy-approximation-Metric-Space A f ε
    in
      monotonic-neighborhood-Metric-Space A x y
        ( ε +ℚ⁺ ε)
        ( δ)
        ( ε+ε<δ)
        ( triangular-neighborhood-Metric-Space A x fε y ε ε
          ( lim-y ε)
          ( symmetric-neighborhood-Metric-Space A ε fε x (lim-x ε)))

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

## See also

- [convergent cauchy approximations](metric-spaces.convergent-cauchy-approximations-metric-spaces.md):
  the type of Cauchy approximations with a limit.

## References

Our definition of limit of Cauchy approximation follows Definition 11.2.10 of
{{#cite UF13}}.

{{#bibliography}}
