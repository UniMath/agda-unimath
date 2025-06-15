# Series

```agda
module analysis.series where
```

<details><summary>Imports</summary>

```agda
open import analysis.commutative-rings-in-complete-metric-spaces

open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sequences
open import foundation.universe-levels

open import metric-spaces.limits-of-sequences-metric-spaces

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A series is an infinite sum taken over the natural numbers. If it has a limit,
it is said to converge, otherwise it is said to diverge.

## Definition

```agda
record
  series
    {l1 l2 : Level} (RM : Commutative-Ring-In-Complete-Metric-Space l1 l2) :
    UU l1
  where

  constructor series-terms

  field
    terms-series : sequence (type-Commutative-Ring-In-Complete-Metric-Space RM)

open series public

module _
  {l1 l2 : Level}
  (RM : Commutative-Ring-In-Complete-Metric-Space l1 l2) (σ : series RM)
  where

  partial-sums-series :
    sequence (type-Commutative-Ring-In-Complete-Metric-Space RM)
  partial-sums-series n =
    sum-fin-sequence-type-Commutative-Ring
      ( commutative-ring-Commutative-Ring-In-Complete-Metric-Space RM)
      ( n)
      ( λ k → terms-series σ (nat-Fin n k))

  converges-series : UU (l1 ⊔ l2)
  converges-series =
    has-limit-sequence-Metric-Space
      ( metric-space-Commutative-Ring-In-Complete-Metric-Space RM)
      ( partial-sums-series)

  is-prop-converges-series : is-prop converges-series
  is-prop-converges-series =
    is-prop-has-limit-sequence-Metric-Space
      ( metric-space-Commutative-Ring-In-Complete-Metric-Space RM)
      ( partial-sums-series)

  converges-prop-series : Prop (l1 ⊔ l2)
  pr1 converges-prop-series = converges-series
  pr2 converges-prop-series = is-prop-converges-series
```
