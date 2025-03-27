# Limits of sequences in metric spaces

```agda
module metric-spaces.limits-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.limits-sequences-premetric-spaces
open import metric-spaces.limits-sequences-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.sequences-metric-spaces
```

</details>

## Ideas

{{#concept "Limits" Disambiguation="of sequences in metric spaces" Agda=is-limit-sequence-Metric-Space}}
of [sequences in metric spaces](metric-spaces.sequences-metric-spaces.md) are
[limits](metric-spaces.limits-sequences-premetric-spaces.md) in the underlying
[premetric space](metric-spaces.premetric-spaces.md).

Limits of a sequence in a metric space are unique.

## Definition

### Limits of sequences in metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : sequence-Metric-Space M)
  (l : type-Metric-Space M)
  where

  is-modulus-limit-sequence-Metric-Space : ℚ⁺ → ℕ → UU l2
  is-modulus-limit-sequence-Metric-Space =
    is-modulus-limit-sequence-Premetric-Space
      ( premetric-Metric-Space M)
      ( u)
      ( l)

  is-limit-sequence-Metric-Space : UU l2
  is-limit-sequence-Metric-Space =
    is-limit-sequence-Premetric-Space
      ( premetric-Metric-Space M)
      ( u)
      ( l)

  modulus-limit-sequence-Metric-Space :
    is-limit-sequence-Metric-Space → ℚ⁺ → ℕ
  modulus-limit-sequence-Metric-Space =
    modulus-limit-sequence-Premetric-Space
      ( premetric-Metric-Space M)
      ( u)
      ( l)

  is-modulus-modulus-limit-sequence-Metric-Space :
    (H : is-limit-sequence-Metric-Space) (d : ℚ⁺) →
    (n : ℕ) (I : leq-ℕ (modulus-limit-sequence-Metric-Space H d) n) →
    neighborhood-Metric-Space M d (u n) l
  is-modulus-modulus-limit-sequence-Metric-Space =
    is-modulus-modulus-limit-sequence-Premetric-Space
      ( premetric-Metric-Space M)
      ( u)
      ( l)
```

## Properties

### Two limits of a sequence in a metric space are equal

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : sequence-Metric-Space M)
  (x y : type-Metric-Space M)
  (Lx : is-limit-sequence-Metric-Space M u x)
  (Ly : is-limit-sequence-Metric-Space M u y)
  where

  eq-limit-sequence-Metric-Space : x ＝ y
  eq-limit-sequence-Metric-Space =
    is-tight-structure-Metric-Space M x y
      (indistinguishable-limit-sequence-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( u)
        ( x)
        ( y)
        ( Lx)
        ( Ly))
```
