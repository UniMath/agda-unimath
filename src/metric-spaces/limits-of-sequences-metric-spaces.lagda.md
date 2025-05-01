# Limits of sequences in metric spaces

```agda
module metric-spaces.limits-of-sequences-metric-spaces where
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

open import metric-spaces.limits-of-sequences-premetric-spaces
open import metric-spaces.limits-of-sequences-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.sequences-metric-spaces
```

</details>

## Ideas

{{#concept "Limits" Disambiguation="of sequences in metric spaces" WD="limit of a sequence" WDID=Q847204 Agda=is-limit-sequence-Metric-Space}}
of [sequences in metric spaces](metric-spaces.sequences-metric-spaces.md) are
[limits](metric-spaces.limits-of-sequences-premetric-spaces.md) in the
underlying [premetric space](metric-spaces.premetric-spaces.md): there exists a
function `m : ℚ⁺ → ℕ` such that whenever `m ε ≤ n` in `ℕ`, `u n` is in an
[`ε`-neighborhood](metric-spaces.premetric-structures.md) of `l`. In a metric
space, all limits of a sequence are [equal](foundation.identity-types.md).

## Definition

### Limits of sequences in a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : sequence-type-Metric-Space M)
  (l : type-Metric-Space M)
  where

  is-limit-modulus-prop-sequence-Metric-Space : (ℚ⁺ → ℕ) → Prop l2
  is-limit-modulus-prop-sequence-Metric-Space =
    is-limit-modulus-prop-sequence-Premetric-Space
      ( premetric-Metric-Space M)
      ( u)
      ( l)

  is-limit-modulus-sequence-Metric-Space : (ℚ⁺ → ℕ) → UU l2
  is-limit-modulus-sequence-Metric-Space m =
    type-Prop (is-limit-modulus-prop-sequence-Metric-Space m)

  limit-modulus-sequence-Metric-Space : UU l2
  limit-modulus-sequence-Metric-Space =
    type-subtype is-limit-modulus-prop-sequence-Metric-Space

  modulus-limit-modulus-sequence-Metric-Space :
    limit-modulus-sequence-Metric-Space → ℚ⁺ → ℕ
  modulus-limit-modulus-sequence-Metric-Space m = pr1 m

  is-modulus-limit-modulus-sequence-Metric-Space :
    (m : limit-modulus-sequence-Metric-Space) →
    is-limit-modulus-sequence-Metric-Space
      (modulus-limit-modulus-sequence-Metric-Space m)
  is-modulus-limit-modulus-sequence-Metric-Space m = pr2 m

  is-limit-prop-sequence-Metric-Space : Prop l2
  is-limit-prop-sequence-Metric-Space =
    is-inhabited-subtype-Prop is-limit-modulus-prop-sequence-Metric-Space

  is-limit-sequence-Metric-Space : UU l2
  is-limit-sequence-Metric-Space =
    type-Prop is-limit-prop-sequence-Metric-Space
```

## Properties

### The limit of a sequence in a metric space is unique

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

## See also

- [Convergent sequences](metric-spaces.convergent-sequences-metric-spaces.md):
  the type of sequences that have a limit
- The
  [metric space of convergent sequences](metric-spaces.metric-space-of-convergent-sequences-metric-spaces.md):
  the metric structure on the type of convergent sequences

## External links

- [Limit of a sequence](https://en.wikipedia.org/wiki/Limit_of_a_sequence) at
  Wikipedia
