# Sequences in metric spaces

```agda
module metric-spaces.sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.sequences
open import foundation.universe-levels

open import metric-spaces.metric-spaces
```

</details>

## Idea

A
{{#concept "sequence" Disambiguation="in a metric space" Agda=sequence-Metric-Space}}
in a [metric space](metric-spaces.metric-spaces.md) is a
[sequence in its underlying pseudometric space](metric-spaces.sequences-pseudometric-spaces.md).

Two sequences `u v : sequence-Metric-Space M` are
{{#concept "asymptotically indistinguishable" Disambiguation="sequences in a metric space" Agda=is-asymptotically-indistinguishable-sequence-Metric-Space}}
if they are as [sequences](metric-spaces.sequences-premetric-spaces.md) in the
underlying [premetric space](metric-spaces.premetric-spaces.md).

## Definitions

### Sequences in metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  sequence-Metric-Space : UU l1
  sequence-Metric-Space = sequence (type-Metric-Space M)
```

### Asymptotically indistinguishable sequences in a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u v : sequence-Metric-Space M)
  where

  is-modulus-asymptotically-indistinguishable-sequence-Metric-Space :
    (d : ℚ⁺) (N : ℕ) → UU l2
  is-modulus-asymptotically-indistinguishable-sequence-Metric-Space d N =
    (n : ℕ) → leq-ℕ N n → neighborhood-Metric-Space M d (u n) (v n)

  has-modulus-asymptotically-indistinguishable-sequence-Metric-Space :
    (d : ℚ⁺) → UU l2
  has-modulus-asymptotically-indistinguishable-sequence-Metric-Space d =
    Σ ( ℕ)
      ( is-modulus-asymptotically-indistinguishable-sequence-Metric-Space
        ( d))

  is-asymptotically-indistinguishable-sequence-Metric-Space : UU l2
  is-asymptotically-indistinguishable-sequence-Metric-Space =
    (d : ℚ⁺) →
    has-modulus-asymptotically-indistinguishable-sequence-Metric-Space d
```
