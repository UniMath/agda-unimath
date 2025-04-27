# Limits of sequences in metric spaces

```agda
module metric-spaces.limits-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.subtypes
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
In a metric space, all limits of a sequence are equal.

## Definition

### Limits of sequences in metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : sequence-type-Metric-Space M)
  (l : type-Metric-Space M)
  where

  is-modulus-limit-prop-sequence-Metric-Space : (ℚ⁺ → ℕ) → Prop l2
  is-modulus-limit-prop-sequence-Metric-Space =
    is-modulus-limit-prop-sequence-Premetric-Space
      ( premetric-Metric-Space M)
      ( u)
      ( l)

  is-modulus-limit-sequence-Metric-Space : (ℚ⁺ → ℕ) → UU l2
  is-modulus-limit-sequence-Metric-Space m =
    type-Prop (is-modulus-limit-prop-sequence-Metric-Space m)

  modulus-limit-sequence-Metric-Space : UU l2
  modulus-limit-sequence-Metric-Space =
    type-subtype is-modulus-limit-prop-sequence-Metric-Space

  modulus-modulus-limit-sequence-Metric-Space :
    modulus-limit-sequence-Metric-Space → ℚ⁺ → ℕ
  modulus-modulus-limit-sequence-Metric-Space m = pr1 m

  is-modulus-modulus-limit-sequence-Metric-Space :
    (m : modulus-limit-sequence-Metric-Space) →
    is-modulus-limit-sequence-Metric-Space
      (modulus-modulus-limit-sequence-Metric-Space m)
  is-modulus-modulus-limit-sequence-Metric-Space m = pr2 m

  is-limit-prop-sequence-Metric-Space : Prop l2
  is-limit-prop-sequence-Metric-Space =
    is-inhabited-subtype-Prop is-modulus-limit-prop-sequence-Metric-Space

  is-limit-sequence-Metric-Space : UU l2
  is-limit-sequence-Metric-Space =
    type-Prop is-limit-prop-sequence-Metric-Space
```

## Properties

### Two limits of a sequence in a metric space are equal

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : sequence-type-Metric-Space M)
  (x y : type-Metric-Space M)
  (Lx : is-limit-sequence-Metric-Space M u x)
  (Ly : is-limit-sequence-Metric-Space M u y)
  where

  eq-limit-sequence-Metric-Space : x ＝ y
  eq-limit-sequence-Metric-Space =
    is-tight-structure-Metric-Space M x y
      ( indistinguishable-limit-sequence-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( u)
        ( x)
        ( y)
        ( Lx)
        ( Ly))
```

### Having a limit in a metric space is a proposition

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : sequence-type-Metric-Space M)
  where

  has-limit-sequence-Metric-Space : UU (l1 ⊔ l2)
  has-limit-sequence-Metric-Space =
    Σ (type-Metric-Space M) (is-limit-sequence-Metric-Space M u)

  limit-has-limit-sequence-Metric-Space :
    has-limit-sequence-Metric-Space → type-Metric-Space M
  limit-has-limit-sequence-Metric-Space H = pr1 H

  is-limit-limit-has-limit-sequence-Metric-Space :
    (H : has-limit-sequence-Metric-Space) →
    is-limit-sequence-Metric-Space M u
      (limit-has-limit-sequence-Metric-Space H)
  is-limit-limit-has-limit-sequence-Metric-Space H = pr2 H

  is-prop-has-limit-sequence-Metric-Space :
    is-prop has-limit-sequence-Metric-Space
  is-prop-has-limit-sequence-Metric-Space =
    is-prop-all-elements-equal
      ( λ x y →
        eq-type-subtype
          ( is-limit-prop-sequence-Metric-Space M u)
          ( eq-limit-sequence-Metric-Space M u
            ( limit-has-limit-sequence-Metric-Space x)
            ( limit-has-limit-sequence-Metric-Space y)
            ( is-limit-limit-has-limit-sequence-Metric-Space x)
            ( is-limit-limit-has-limit-sequence-Metric-Space y)))

  has-limit-prop-sequence-Metric-Space : Prop (l1 ⊔ l2)
  has-limit-prop-sequence-Metric-Space =
    has-limit-sequence-Metric-Space ,
    is-prop-has-limit-sequence-Metric-Space
```
