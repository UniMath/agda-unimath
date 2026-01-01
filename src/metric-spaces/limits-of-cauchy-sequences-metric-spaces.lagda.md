# Limits of Cauchy sequences in metric spaces

```agda
module metric-spaces.limits-of-cauchy-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.cauchy-sequences-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

An element `l` of a [metric space](metric-spaces.metric-spaces.md) is the
{{#concept "limit" Disambiguation="of a Cauchy sequence in a metric spaces" Agda=is-limit-cauchy-sequence-Metric-Space}}
of a [Cauchy sequence](metric-spaces.cauchy-sequences-metric-spaces.md) `u` in
the metric space if there [exists](foundation.existential-quantification.md) a
function `m : ℚ⁺ → ℕ` such that whenever `m ε ≤ n` in `ℕ`, `u n` is in an
[`ε`-neighborhood](metric-spaces.rational-neighborhood-relations.md) of `l`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  (x : cauchy-sequence-Metric-Space M)
  where

  is-limit-modulus-prop-cauchy-sequence-Metric-Space :
    type-Metric-Space M → (ℚ⁺ → ℕ) → Prop l2
  is-limit-modulus-prop-cauchy-sequence-Metric-Space =
    is-limit-modulus-prop-sequence-Metric-Space
      ( M)
      ( seq-cauchy-sequence-Metric-Space M x)

  is-limit-modulus-cauchy-sequence-Metric-Space :
    type-Metric-Space M → (ℚ⁺ → ℕ) → UU l2
  is-limit-modulus-cauchy-sequence-Metric-Space lim μ =
    type-Prop (is-limit-modulus-prop-cauchy-sequence-Metric-Space lim μ)

  limit-modulus-seq-cauchy-sequence-Metric-Space :
    type-Metric-Space M → UU l2
  limit-modulus-seq-cauchy-sequence-Metric-Space lim =
    type-subtype (is-limit-modulus-prop-cauchy-sequence-Metric-Space lim)

  is-limit-prop-cauchy-sequence-Metric-Space :
    type-Metric-Space M → Prop l2
  is-limit-prop-cauchy-sequence-Metric-Space =
    is-limit-prop-sequence-Metric-Space
      ( M)
      ( seq-cauchy-sequence-Metric-Space M x)

  is-limit-cauchy-sequence-Metric-Space : type-Metric-Space M → UU l2
  is-limit-cauchy-sequence-Metric-Space lim =
    type-Prop (is-limit-prop-cauchy-sequence-Metric-Space lim)

  has-limit-prop-cauchy-sequence-Metric-Space : Prop (l1 ⊔ l2)
  has-limit-prop-cauchy-sequence-Metric-Space =
    has-limit-prop-sequence-Metric-Space
      ( M)
      ( seq-cauchy-sequence-Metric-Space M x)

  has-limit-cauchy-sequence-Metric-Space : UU (l1 ⊔ l2)
  has-limit-cauchy-sequence-Metric-Space =
    type-Prop has-limit-prop-cauchy-sequence-Metric-Space
```
