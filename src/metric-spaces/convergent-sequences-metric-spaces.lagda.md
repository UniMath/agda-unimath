# Convergent sequences in metric spaces

```agda
module metric-spaces.convergent-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.limits-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

A [sequence](metric-spaces.sequences-metric-spaces.md) in a
[metric space](metric-spaces.metric-spaces.md) is
{{#concept "convergent" Disambiguation="sequence in metric spaces" Agda=is-convergent-sequence-Metric-Space}}
if it has a [limit](metric-spaces.limits-sequences-metric-spaces.md).

## Definitions

### Convergent sequences in metric spaces

```agda
module _
  {l : Level} (M : Metric-Space l)
  where

  is-convergent-sequence-Metric-Space : sequence-Metric-Space M → UU l
  is-convergent-sequence-Metric-Space u =
    Σ (type-Metric-Space M) (is-limit-sequence-Metric-Space M u)

  convergent-sequence-Metric-Space : UU l
  convergent-sequence-Metric-Space =
    Σ (sequence-Metric-Space M) is-convergent-sequence-Metric-Space

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

  modulus-convergent-sequence-Metric-Space : ℚ⁺ → ℕ
  modulus-convergent-sequence-Metric-Space =
    modulus-limit-sequence-Metric-Space M
      sequence-convergent-sequence-Metric-Space
      limit-convergent-sequence-Metric-Space
      is-limit-convergent-sequence-Metric-Space

  is-modulus-modulus-convergent-sequence-Metric-Space :
    (d : ℚ⁺) →
    is-modulus-limit-sequence-Metric-Space M
      ( sequence-convergent-sequence-Metric-Space)
      ( limit-convergent-sequence-Metric-Space)
      ( d)
      ( modulus-convergent-sequence-Metric-Space d)
  is-modulus-modulus-convergent-sequence-Metric-Space =
    is-modulus-modulus-limit-sequence-Metric-Space M
      ( sequence-convergent-sequence-Metric-Space)
      ( limit-convergent-sequence-Metric-Space)
      ( is-limit-convergent-sequence-Metric-Space)
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
