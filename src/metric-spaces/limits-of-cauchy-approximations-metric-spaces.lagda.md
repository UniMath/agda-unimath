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
{{#concept "limit" Disambiguation="of a Cauchy approximation in a metric space" Agda=is-limit-cauchy-approximation-Metric-Space}}
`x : A` if `f ε` is near `x` for small `ε : ℚ⁺`. More precisely, `f` has a limit if `f ε` is in
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
        Π-Prop
          ( ℚ⁺)
          ( λ δ →
            neighborhood-prop-Metric-Space
              ( A)
              ( ε +ℚ⁺ δ)
              ( map-cauchy-approximation-Metric-Space A f ε)
              ( lim)))

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
  all-sim-is-limit-cauchy-approximation-Metric-Space lim-x lim-y d =
    let
      (ε , δ , ε+δ=d) = split-ℚ⁺ d
      θ = mediant-zero-min-ℚ⁺ ε δ
      θ<ε = le-left-mediant-zero-min-ℚ⁺ ε δ
      θ<δ = le-right-mediant-zero-min-ℚ⁺ ε δ
      ε' = le-diff-ℚ⁺ θ ε θ<ε
      δ' = le-diff-ℚ⁺ θ δ θ<δ
      fθ = map-cauchy-approximation-Metric-Space A f θ

      Nεx : neighborhood-Metric-Space A ε fθ x
      Nεx =
        tr
          ( is-upper-bound-dist-Metric-Space A fθ x)
          ( right-diff-law-add-ℚ⁺ θ ε θ<ε)
          ( lim-x θ ε')

      Nδy : neighborhood-Metric-Space A δ fθ y
      Nδy =
        tr
          ( is-upper-bound-dist-Metric-Space A fθ y)
          ( right-diff-law-add-ℚ⁺ θ δ θ<δ)
          ( lim-y θ δ')

      Nxy : neighborhood-Metric-Space A (ε +ℚ⁺ δ) x y
      Nxy =
        triangular-neighborhood-Metric-Space
          ( A)
          ( x)
          ( fθ)
          ( y)
          ( ε)
          ( δ)
          ( Nδy)
          ( symmetric-neighborhood-Metric-Space A ε fθ x Nεx)
    in
      tr
        ( is-upper-bound-dist-Metric-Space A x y)
        ( ε+δ=d)
        ( Nxy)

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

- [Convergent cauchy approximations](metric-spaces.convergent-cauchy-approximations-metric-spaces.md) are Cauchy approximations with a limit.

## References

Our definition of limit of Cauchy approximation follows Definition 11.2.10 of
{{#cite UF13}}.

{{#bibliography}}
