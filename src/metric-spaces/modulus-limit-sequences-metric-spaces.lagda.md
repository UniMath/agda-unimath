# Limit modulus of sequences in metric spaces

```agda
module metric-spaces.modulus-limit-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.neighbourhood-relations
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

Given a [metric space](metric-spaces.metric-spaces.md) `(M , B)`, a
[natual number](elementary-number-theory.natural-numbers.md) `N` is a
{{#concept "limit modulus"}} of a
[sequence](metric-spaces.sequences-metric-spaces.md) `u : ℕ → M` at the point
`x : M` and distance `d : ℚ⁺` if `B d x (u n)` for all `n : ℕ` greater than N.

## Definitions

### Limit modulus of sequences in metric spaces

```agda
module _
  {l : Level} (M : Metric-Space l) (u : sequence-Metric-Space M)
  (x : type-Metric-Space M) (d : ℚ⁺) (N : ℕ)
  where

  is-modulus-limit-prop-sequence-Metric-Space : Prop l
  is-modulus-limit-prop-sequence-Metric-Space =
    Π-Prop
      ( ℕ)
      ( λ (n : ℕ) →
        hom-Prop (leq-ℕ-Prop N n) (neighbourhood-Metric-Space M d x (u n)))

  is-modulus-limit-sequence-Metric-Space : UU l
  is-modulus-limit-sequence-Metric-Space =
    type-Prop is-modulus-limit-prop-sequence-Metric-Space

  is-prop-is-modulus-limit-sequence-Metric-Space :
    is-prop is-modulus-limit-sequence-Metric-Space
  is-prop-is-modulus-limit-sequence-Metric-Space =
    is-prop-type-Prop is-modulus-limit-prop-sequence-Metric-Space
```
