# Convergent sequences in metric spaces

```agda
module metric-spaces.convergent-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.limit-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulus-limit-sequences-metric-spaces
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

A [sequence](metric-spaces.sequences-metric-spaces.md) in a
[metric space](metric-spaces.metric-spaces.md) is
{{#concept "convergent" Disambiguation="sequence in metric spaces" Agda=is-convergent-sequence-Metric-Space}}
if it has a [limit](metric-spaces.limit-sequences-metric-spaces.md).

## Definitions

### The property of being a convergent sequence

```agda
module _
  {l : Level} (M : Metric-Space l) (u : sequence-Metric-Space M)
  where

  is-convergent-sequence-Metric-Space : UU l
  is-convergent-sequence-Metric-Space =
    type-subtype (is-limit-prop-sequence-Metric-Space M u)

  is-prop-is-convergent-sequence-Metric-Space :
    is-prop is-convergent-sequence-Metric-Space
  is-prop-is-convergent-sequence-Metric-Space =
    is-prop-all-elements-equal
      ( λ x y →
        eq-type-subtype
          ( is-limit-prop-sequence-Metric-Space M u)
          ( eq-limit-sequence-Metric-Space
            ( M)
            ( u)
            ( pr1 x)
            ( pr1 y)
            ( pr2 x)
            ( pr2 y)))

  is-convergent-prop-sequence-Metric-Space : Prop l
  is-convergent-prop-sequence-Metric-Space =
    is-convergent-sequence-Metric-Space ,
    is-prop-is-convergent-sequence-Metric-Space
```

### Convergent sequences in metric spaces

```agda
module _
  {l : Level} (M : Metric-Space l)
  where
  convergent-sequence-Metric-Space : UU l
  convergent-sequence-Metric-Space =
    type-subtype (is-convergent-prop-sequence-Metric-Space M)

module _
  {l : Level} (M : Metric-Space l) (u : convergent-sequence-Metric-Space M)
  where

  sequence-convergent-sequence-Metric-Space : sequence-Metric-Space M
  sequence-convergent-sequence-Metric-Space = pr1 u

  limit-convergent-sequence-Metric-Space : type-Metric-Space M
  limit-convergent-sequence-Metric-Space = pr1 (pr2 u)

  is-limit-convergent-sequence-Metric-Space :
    is-limit-sequence-Metric-Space M
      sequence-convergent-sequence-Metric-Space
      limit-convergent-sequence-Metric-Space
  is-limit-convergent-sequence-Metric-Space = pr2 (pr2 u)

  modulus-limit-convergent-sequence-Metric-Space :
    (d : ℚ⁺) →
    ║ Σ ( ℕ)
        ( is-modulus-limit-sequence-Metric-Space
          ( M)
          ( sequence-convergent-sequence-Metric-Space)
          ( limit-convergent-sequence-Metric-Space)
          ( d)) ║₋₁
  modulus-limit-convergent-sequence-Metric-Space d =
    is-limit-convergent-sequence-Metric-Space d
```

### Constant sequences in metric spaces are convergent

```agda
module _
  {l : Level} (M : Metric-Space l) (x : type-Metric-Space M)
  where

  is-convergent-constant-sequence-Metric-Space :
    is-convergent-sequence-Metric-Space M (constant-sequence-Metric-Space M x)
  is-convergent-constant-sequence-Metric-Space =
    (x , is-limit-constant-sequence-Metric-Space M x)
```
