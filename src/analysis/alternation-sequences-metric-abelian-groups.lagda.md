# The alternation of sequences in metric abelian groups

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.alternation-sequences-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.limits-of-sequences-metric-abelian-groups
open import analysis.metric-abelian-groups
open import analysis.series-metric-abelian-groups

open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.coproduct-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.involutions
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences

open import logic.functoriality-existential-quantification
```

</details>

## Idea

The
{{#concept "alternation" Disambiguation="of a sequence in a metric abelian group" Agda=alternation-sequence-Metric-Ab}}
of a [sequence](lists.sequences.md) `aₙ` in a
[metric abelian group](analysis.metric-abelian-groups.md) is the sequence `bₙ`
where `bₙ = aₙ` if `n` is
[even](elementary-number-theory.parity-natural-numbers.md), and `bₙ = -aₙ` if
`n` is odd.

## Definition

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  alternation-sequence-Metric-Ab :
    sequence (type-Metric-Ab G) → sequence (type-Metric-Ab G)
  alternation-sequence-Metric-Ab a n =
    rec-coproduct
      ( λ _ → a n)
      ( λ _ → neg-Metric-Ab G (a n))
      ( is-decidable-is-even-ℕ n)
```

## Properties

### If `aₙ` has a limit of 0, so does the alternating sequence

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  {a : sequence (type-Metric-Ab G)}
  where

  abstract
    preserves-is-limit-zero-modulus-alternation-sequence-Metric-Ab :
      (μ : ℚ⁺ → ℕ) →
      is-limit-modulus-sequence-Metric-Ab G a (zero-Metric-Ab G) μ →
      is-limit-modulus-sequence-Metric-Ab
        ( G)
        ( alternation-sequence-Metric-Ab G a)
        ( zero-Metric-Ab G)
        ( μ)
    preserves-is-limit-zero-modulus-alternation-sequence-Metric-Ab
      μ is-mod-μ ε n με≤n with is-decidable-is-even-ℕ n
    ... | inl even = is-mod-μ ε n με≤n
    ... | inr odd =
      tr
        ( neighborhood-Metric-Ab G ε (neg-Metric-Ab G (a n)))
        ( neg-zero-Metric-Ab G)
        ( forward-implication
          ( is-isometry-neg-Metric-Ab G ε (a n) (zero-Metric-Ab G))
          ( is-mod-μ ε n με≤n))

    preserves-is-limit-zero-alternation-sequence-Metric-Ab :
      is-limit-sequence-Metric-Ab G a (zero-Metric-Ab G) →
      is-limit-sequence-Metric-Ab
        ( G)
        ( alternation-sequence-Metric-Ab G a)
        ( zero-Metric-Ab G)
    preserves-is-limit-zero-alternation-sequence-Metric-Ab =
      map-tot-exists
        ( preserves-is-limit-zero-modulus-alternation-sequence-Metric-Ab)
```

### Alternating a sequence is an involution

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  abstract
    htpy-is-involution-alternation-sequence-Metric-Ab :
      (σ : sequence (type-Metric-Ab G)) →
      alternation-sequence-Metric-Ab G (alternation-sequence-Metric-Ab G σ) ~ σ
    htpy-is-involution-alternation-sequence-Metric-Ab σ n
      with is-decidable-is-even-ℕ n
    ... | inl even = refl
    ... | inr odd = neg-neg-Metric-Ab G (σ n)

    is-involution-alternation-sequence-Metric-Ab :
      is-involution (alternation-sequence-Metric-Ab G)
    is-involution-alternation-sequence-Metric-Ab σ =
      eq-htpy (htpy-is-involution-alternation-sequence-Metric-Ab σ)
```
