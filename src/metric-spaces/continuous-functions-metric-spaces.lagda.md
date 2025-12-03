# Continuous functions between metric spaces

```agda
module metric-spaces.continuous-functions-metric-spaces where
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

open import metric-spaces.functions-metric-spaces
open import metric-spaces.limits-of-functions-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) `f` between
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y` is
{{#concept "continuous" Disambiguation="function between metric spaces at a point" WDID=Q170058 WD="continuous function" Agda=is-continuous-at-point-function-Metric-Space}}
at a point `x` if `f x` is the
[limit](metric-spaces.limits-of-functions-metric-spaces.md) of `f` at `x`. I.e.,
there exists a function `m : ℚ⁺ → ℚ⁺` such that whenever `x'` is in an
`m ε`-neighborhood of `x`, `f x'` is in an `ε`-neighborhood of `f x`. In this
case, `m` is called a modulus of continuity of `f` at `x`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y)
  (x : type-Metric-Space X)
  where

  is-continuous-at-point-prop-function-Metric-Space : Prop (l1 ⊔ l2 ⊔ l4)
  is-continuous-at-point-prop-function-Metric-Space =
    is-point-limit-prop-function-Metric-Space X Y f x (f x)

  is-continuous-at-point-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-continuous-at-point-function-Metric-Space =
    is-point-limit-function-Metric-Space X Y f x (f x)

  is-modulus-of-continuity-at-point-prop-function-Metric-Space :
    (ℚ⁺ → ℚ⁺) → Prop (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-continuity-at-point-prop-function-Metric-Space =
    is-modulus-of-point-limit-prop-function-Metric-Space X Y f x (f x)

  is-modulus-of-continuity-at-point-function-Metric-Space :
    (ℚ⁺ → ℚ⁺) → UU (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-continuity-at-point-function-Metric-Space =
    is-modulus-of-point-limit-function-Metric-Space X Y f x (f x)

  modulus-of-continuity-at-point-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  modulus-of-continuity-at-point-function-Metric-Space =
    type-subtype
      is-modulus-of-continuity-at-point-prop-function-Metric-Space

module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y)
  where

  is-pointwise-continuous-prop-function-Metric-Space : Prop (l1 ⊔ l2 ⊔ l4)
  is-pointwise-continuous-prop-function-Metric-Space =
    Π-Prop
      ( type-Metric-Space X)
      ( is-continuous-at-point-prop-function-Metric-Space X Y f)

  is-pointwise-continuous-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-pointwise-continuous-function-Metric-Space =
    type-Prop is-pointwise-continuous-prop-function-Metric-Space
```
