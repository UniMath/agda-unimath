# Limits of maps between metric spaces

```agda
module metric-spaces.limits-of-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A [map](metric-spaces.maps-metric-spaces.md) `f` between
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y` has a
{{#concept "limit" Disambiguation="of a map between metric spaces at a point" Agda=is-point-limit-map-Metric-Space}}
`y : Y` at a point `x : X` if there
[exists](foundation.existential-quantification.md) a function `m : ℚ⁺ → ℚ⁺` such
that whenever `x'` is in an `m ε`-neighborhood of `x`, `f x'` is in an
`ε`-neighborhood of `y`. In this case `m` is called a
{{#concept "limit modulus" Disambiguation="of a map between metric spaces at a point" Agda=is-modulus-of-point-limit-map-Metric-Space}}
of `f` at `x`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : map-Metric-Space X Y)
  (x : type-Metric-Space X)
  (y : type-Metric-Space Y)
  where

  is-modulus-of-point-limit-prop-map-Metric-Space :
    (ℚ⁺ → ℚ⁺) → Prop (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-point-limit-prop-map-Metric-Space m =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
        ( type-Metric-Space X)
        ( λ x' →
          neighborhood-prop-Metric-Space X (m ε) x x' ⇒
          neighborhood-prop-Metric-Space Y ε y (f x')))

  is-modulus-of-point-limit-map-Metric-Space :
    (ℚ⁺ → ℚ⁺) → UU (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-point-limit-map-Metric-Space m =
    type-Prop (is-modulus-of-point-limit-prop-map-Metric-Space m)

  is-point-limit-prop-map-Metric-Space : Prop (l1 ⊔ l2 ⊔ l4)
  is-point-limit-prop-map-Metric-Space =
    is-inhabited-subtype-Prop
      is-modulus-of-point-limit-prop-map-Metric-Space

  is-point-limit-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-point-limit-map-Metric-Space =
    type-Prop is-point-limit-prop-map-Metric-Space
```

## See also

- [ε-δ limits of functions in metric spaces](metric-spaces.epsilon-delta-limits-of-maps-metric-spaces.md)

## External links

- [Limit of a function](https://en.wikipedia.org/wiki/Limit_of_a_function#Functions_on_metric_spaces)
  at Wikipedia
