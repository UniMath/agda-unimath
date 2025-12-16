# Alternation of sequences of real numbers

```agda
module real-numbers.alternation-sequences-real-numbers where
```

<details><summary>Imports</summary>
```agda
open import lists.sequences
open import real-numbers.dedekind-real-numbers
open import foundation.universe-levels
open import real-numbers.rational-real-numbers
open import foundation.conjunction
open import real-numbers.raising-universe-levels-real-numbers
open import foundation.propositions
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.nonpositive-real-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import real-numbers.metric-additive-group-of-real-numbers
open import analysis.alternation-sequences-metric-abelian-groups
open import elementary-number-theory.multiplication-natural-numbers
open import real-numbers.limits-sequences-real-numbers
```
</details>

## Idea

## Definition

```agda
alternation-sequence-ℝ :
  {l : Level} → sequence (ℝ l) → sequence (ℝ l)
alternation-sequence-ℝ {l} = alternation-sequence-Metric-Ab (metric-ab-add-ℝ l)
```

## Properties

### If a sequence has a limit of 0, so does its alternation

```agda
abstract
  preserves-is-limit-zero-alternation-sequence-ℝ :
    {l : Level} {u : sequence (ℝ l)} →
    is-limit-sequence-ℝ u (raise-ℝ l zero-ℝ) →
    is-limit-sequence-ℝ (alternation-sequence-ℝ u) (raise-ℝ l zero-ℝ)
  preserves-is-limit-zero-alternation-sequence-ℝ {l} {u} =
    preserves-is-limit-zero-alternation-sequence-Metric-Ab
      ( metric-ab-add-ℝ l)
```
