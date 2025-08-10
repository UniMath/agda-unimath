# Series in semirings

```agda
module ring-theory.series-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sequences
open import foundation.universe-levels

open import lists.finite-sequences

open import ring-theory.semirings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings
```

</details>

## Ideas

A {{#concept "series" Disambiguation="in a semigroup" Agda=series-Semiring}} in
a [semiring] is a [sequence](foundation.sequences.md) of partial sums

```text
n ↦ Σ (k < n) (u k)
```

of the terms of a sequence `u` in the semiring.

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

### Series in semirings

```agda
module _
  {l : Level} (R : Semiring l)
  where

  opaque
    series-Semiring : UU l
    series-Semiring = ℕ → type-Semiring R

    series-sum-sequence-Semiring : (ℕ → type-Semiring R) → series-Semiring
    series-sum-sequence-Semiring u = u

    seq-series-Semiring : series-Semiring → ℕ → type-Semiring R
    seq-series-Semiring = seq-sum-sequence-Semiring R

    htpy-seq-series-sum-sequence-Semiring :
      (u : ℕ → type-Semiring R) →
      seq-series-Semiring (series-sum-sequence-Semiring u) ~
      seq-sum-sequence-Semiring R u
    htpy-seq-series-sum-sequence-Semiring u n = refl
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
