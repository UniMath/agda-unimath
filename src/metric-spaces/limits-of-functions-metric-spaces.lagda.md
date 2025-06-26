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

open import metric-spaces.metric-spaces-WIP
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) `f` between
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y` has a
{{#concept "limit" Disambiguation="of function between metric spaces at a point" Agda=is-pt-limit-function-Metric-Space-WIP}}
`y : Y` at a point `x : X` if there exists a function `m : ℚ⁺ → ℚ⁺` such that
whenever `x'` is in an `m ε`-neighborhood of `x`, `f x'` is in an
`ε`-neighborhood of `y`. `m` is called a limit modulus of `f` at `x`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space-WIP l1 l2)
  (Y : Metric-Space-WIP l3 l4)
  (f : type-function-Metric-Space-WIP X Y)
  (x : type-Metric-Space-WIP X)
  (y : type-Metric-Space-WIP Y)
  where

  is-modulus-of-pt-limit-prop-function-Metric-Space-WIP :
    (ℚ⁺ → ℚ⁺) → Prop (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-pt-limit-prop-function-Metric-Space-WIP m =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
        ( type-Metric-Space-WIP X)
        ( λ x' →
          neighborhood-prop-Metric-Space-WIP X (m ε) x x' ⇒
          neighborhood-prop-Metric-Space-WIP Y ε y (f x')))

  is-modulus-of-pt-limit-function-Metric-Space-WIP :
    (ℚ⁺ → ℚ⁺) → UU (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-pt-limit-function-Metric-Space-WIP m =
    type-Prop (is-modulus-of-pt-limit-prop-function-Metric-Space-WIP m)

  is-pt-limit-prop-function-Metric-Space-WIP : Prop (l1 ⊔ l2 ⊔ l4)
  is-pt-limit-prop-function-Metric-Space-WIP =
    is-inhabited-subtype-Prop
      is-modulus-of-pt-limit-prop-function-Metric-Space-WIP

  is-pt-limit-function-Metric-Space-WIP : UU (l1 ⊔ l2 ⊔ l4)
  is-pt-limit-function-Metric-Space-WIP =
    type-Prop is-pt-limit-prop-function-Metric-Space-WIP
```
