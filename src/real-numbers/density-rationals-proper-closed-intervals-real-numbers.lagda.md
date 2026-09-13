# The density of rational numbers in proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.density-rationals-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.dense-subsets-metric-spaces

open import real-numbers.addition-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.dense-subsets-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-approximates-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The [rational real numbers](real-numbers.rational-real-numbers.md) are
[dense](real-numbers.dense-subsets-real-numbers.md) in any
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md).

## Proof

```agda
abstract
  is-dense-subset-rational-proper-closed-interval-ℝ :
    {l1 l2 : Level} (l3 : Level) ([a,b] : proper-closed-interval-ℝ l1 l2) →
    is-dense-subset-Metric-Space
      ( metric-space-proper-closed-interval-ℝ l3 [a,b])
      ( subtype-rational-ℝ ∘ pr1)
  is-dense-subset-rational-proper-closed-interval-ℝ l =
    is-dense-subset-proper-closed-interval-ℝ (dense-subset-rational-ℝ l)
```
