# Alternation of sequences of real numbers

```agda
module real-numbers.alternation-sequences-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.alternation-sequences-metric-abelian-groups

open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import lists.sequences

open import real-numbers.dedekind-real-numbers
open import real-numbers.limits-sequences-real-numbers
open import real-numbers.metric-additive-group-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.nonpositive-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

The
{{#concept "alternation" Disambiguation="of a sequence in ℝ" Agda=alternation-sequence-ℝ}}
of a [sequence](lists.sequences.md) of
[real numbers](real-numbers.dedekind-real-numbers.md) `aₙ` is a sequence `bₙ`
where `bₙ = aₙ` if `n` is
[even](elementary-number-theory.parity-natural-numbers.md), and `bₙ = -aₙ` if
`n` is odd.

## Definition

```agda
alternation-sequence-ℝ :
  {l : Level} → sequence (ℝ l) → sequence (ℝ l)
alternation-sequence-ℝ {l} = alternation-sequence-Metric-Ab (metric-ab-add-ℝ l)
```

## Properties

### Alternation is an involution

```agda
module _
  {l : Level}
  (u : sequence (ℝ l))
  where

  abstract
    is-involution-alternation-sequence-ℝ :
      alternation-sequence-ℝ (alternation-sequence-ℝ u) ＝ u
    is-involution-alternation-sequence-ℝ =
      is-involution-alternation-sequence-Metric-Ab (metric-ab-add-ℝ l) u
```

### The value of the alternation sequence in terms of the parity of the index

```agda
module _
  {l : Level}
  (u : sequence (ℝ l))
  where

  abstract
    eq-alternation-sequence-is-even-ℝ :
      (n : ℕ) → is-even-ℕ n → alternation-sequence-ℝ u n ＝ u n
    eq-alternation-sequence-is-even-ℝ n even
      with is-decidable-is-even-ℕ n
    ... | inl _ = refl
    ... | inr odd = ex-falso (odd even)

    eq-neg-alternation-sequence-is-odd-ℝ :
      (n : ℕ) → is-odd-ℕ n → alternation-sequence-ℝ u n ＝ neg-ℝ (u n)
    eq-neg-alternation-sequence-is-odd-ℝ n odd
      with is-decidable-is-even-ℕ n
    ... | inl even = ex-falso (odd even)
    ... | inr odd = refl
```

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
