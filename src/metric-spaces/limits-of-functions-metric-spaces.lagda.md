# Limits of functions between metric spaces

```agda
module metric-spaces.limits-of-functions-metric-spaces where
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
open import metric-spaces.metric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) `f` between
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y` has a
{{#concept "limit" Disambiguation="of function between metric spaces at a point" Agda=is-pt-limit-function-Metric-Space}}
`y : Y` at a point `x : X` if there exists a function `m : ℚ⁺ → ℚ⁺` such that
whenever `x'` is in an `m ε`-neighborhood of `x`, `f x'` is in an
`ε`-neighborhood of `y`. In this case `m` is called a limit modulus of `f` at `x`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y)
  (x : type-Metric-Space X)
  (y : type-Metric-Space Y)
  where

  is-modulus-of-pt-limit-prop-function-Metric-Space :
    (ℚ⁺ → ℚ⁺) → Prop (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-pt-limit-prop-function-Metric-Space m =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
        ( type-Metric-Space X)
        ( λ x' →
          neighborhood-prop-Metric-Space X (m ε) x x' ⇒
          neighborhood-prop-Metric-Space Y ε y (f x')))

  is-modulus-of-pt-limit-function-Metric-Space :
    (ℚ⁺ → ℚ⁺) → UU (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-pt-limit-function-Metric-Space m =
    type-Prop (is-modulus-of-pt-limit-prop-function-Metric-Space m)

  is-pt-limit-prop-function-Metric-Space : Prop (l1 ⊔ l2 ⊔ l4)
  is-pt-limit-prop-function-Metric-Space =
    is-inhabited-subtype-Prop
      is-modulus-of-pt-limit-prop-function-Metric-Space

  is-pt-limit-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-pt-limit-function-Metric-Space =
    type-Prop is-pt-limit-prop-function-Metric-Space
```
