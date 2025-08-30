# Partial sums of sequences in semirings

```agda
module ring-theory.partial-sums-sequences-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.sequences

open import ring-theory.semirings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings
```

</details>

## Ideas

The
{{#concept "sequence of partial sums" Disambiguation="of a sequence in a semiring" Agda=seq-sum-sequence-Semiring}}
of a [sequence](lists.sequences.md) `u` in a
[semiring](ring-theory.semirings.md) is the sequence of sums of terms of `u`:

```text
n ↦ Σ (k ≤ n) (u k).
```

## Definitions

### Partial sums of terms of a sequence in a semiring

```agda
module _
  {l : Level} (R : Semiring l) (u : ℕ → type-Semiring R)
  where

  seq-sum-sequence-Semiring : ℕ → type-Semiring R
  seq-sum-sequence-Semiring n =
    sum-fin-sequence-type-Semiring
      ( R)
      ( succ-ℕ n)
      ( fin-sequence-sequence u (succ-ℕ n))
```

## Properties

### Homotopic sequences have homotopic partial sums

```agda
module _
  {l : Level} (R : Semiring l) {u v : ℕ → type-Semiring R}
  where

  htpy-seq-sum-sequence-Semiring :
    (u ~ v) →
    seq-sum-sequence-Semiring R u ~ seq-sum-sequence-Semiring R v
  htpy-seq-sum-sequence-Semiring H n =
    htpy-sum-fin-sequence-type-Semiring
      ( R)
      ( succ-ℕ n)
      ( htpy-fin-sequence-sequence u v H (succ-ℕ n))
```
