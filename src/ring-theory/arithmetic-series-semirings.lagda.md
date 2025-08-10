# Arithmetic series in semirings

```agda
module ring-theory.arithmetic-series-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.function-types
open import foundation.homotopies
open import foundation.universe-levels

open import ring-theory.arithmetic-sequences-semirings
open import ring-theory.semirings
open import ring-theory.series-semirings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings
```

</details>

## Ideas

An
{{#concept "arithmetic series" Disambiguation="in a semiring" Agda=arithmetic-series-Semiring}}
in a [semiring](ring-theory.semirings.md) is a
[series](ring-theory.series-semirings.md) of the partial sums:

```text
n ↦ Σ (k < n) (u k)
```

for some [arithmetic sequence](ring-theory.arithmetic-sequences-semirings.md)
`u` in the semiring. These are the sums

```text
n ↦ Σ (k < n) (a + d * k)
```

for some elements `a d : R` in the semiring.

## Definitions

### Arithmetic series in semirings

```agda
module _
  {l : Level} (R : Semiring l)
  where

  opaque
    arithmetic-series-Semiring : UU l
    arithmetic-series-Semiring = arithmetic-sequence-Semiring R

    arithmetic-series-arithmetic-sequence-Semiring :
      arithmetic-sequence-Semiring R → arithmetic-series-Semiring
    arithmetic-series-arithmetic-sequence-Semiring u = u

    series-arithmetic-series-Semiring :
      arithmetic-series-Semiring → series-Semiring R
    series-arithmetic-series-Semiring =
      series-sum-sequence-Semiring R ∘
      seq-arithmetic-sequence-Semiring R

    arithmetic-terms-arithmetic-series-Semiring :
      arithmetic-series-Semiring → arithmetic-sequence-Semiring R
    arithmetic-terms-arithmetic-series-Semiring u = u

    seq-terms-arithmetic-series-Semiring :
      arithmetic-series-Semiring → ℕ → type-Semiring R
    seq-terms-arithmetic-series-Semiring =
      seq-arithmetic-sequence-Semiring R

  seq-arithmetic-series-Semiring :
    arithmetic-series-Semiring → ℕ → type-Semiring R
  seq-arithmetic-series-Semiring =
    seq-series-Semiring R ∘ series-arithmetic-series-Semiring
```

### The partial sums of terms of an arithmetic sequence in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  seq-sum-arithmetic-sequence-Semiring :
    arithmetic-sequence-Semiring R → ℕ → type-Semiring R
  seq-sum-arithmetic-sequence-Semiring =
    seq-sum-sequence-Semiring R ∘
    seq-arithmetic-sequence-Semiring R
```

### The partial sums of terms of a standard arithmetic sequence in a semiring

```agda
module _
  {l : Level} (R : Semiring l) (a d : type-Semiring R)
  where

  seq-sum-standard-arithmetic-sequence-Semiring : ℕ → type-Semiring R
  seq-sum-standard-arithmetic-sequence-Semiring =
    seq-sum-arithmetic-sequence-Semiring
      ( R)
      ( standard-arithmetic-sequence-Semiring R a d)
```

### The sums `Σ (i < n) (a + d * i)`

```agda
module _
  {l : Level} (R : Semiring l) (a d : type-Semiring R)
  where

  seq-sum-add-mul-nat-Semiring : ℕ → type-Semiring R
  seq-sum-add-mul-nat-Semiring =
    seq-sum-arithmetic-sequence-Semiring
      ( R)
      ( arithmetic-add-mul-nat-Semiring R a d)
```

## Properties

### The values of an arithmetic series are the partial sums of its arithmetic sequence of terms

```agda
module _
  {l : Level} (R : Semiring l)
  where

  opaque
    unfolding arithmetic-series-Semiring
    unfolding htpy-seq-series-sum-sequence-Semiring

    htpy-seq-arithmetic-series-Semiring :
      ( u : arithmetic-series-Semiring R) →
      ( seq-sum-arithmetic-sequence-Semiring
        ( R)
        ( arithmetic-terms-arithmetic-series-Semiring R u)) ~
      ( seq-arithmetic-series-Semiring R u)
    htpy-seq-arithmetic-series-Semiring u =
      htpy-seq-series-sum-sequence-Semiring
        ( R)
        ( seq-terms-arithmetic-series-Semiring R u)
```

### The sum of terms of an arithmetic sequence is determined by its initial term and common differenence

```agda
module _
  {l : Level} (R : Semiring l)
  where

  htpy-sum-arithmetic-standard-arithmetic-sequence-Semiring :
    (u : arithmetic-sequence-Semiring R) →
    ( seq-sum-standard-arithmetic-sequence-Semiring
      ( R)
      ( initial-term-arithmetic-sequence-Semiring R u)
      ( common-difference-arithmetic-sequence-Semiring R u)) ~
    ( seq-sum-arithmetic-sequence-Semiring R u)
  htpy-sum-arithmetic-standard-arithmetic-sequence-Semiring =
    htpy-seq-sum-sequence-Semiring R ∘
    htpy-seq-standard-arithmetic-sequence-Semiring R
```

### The nth partial sum of terms of the standard arithmetic sequence with initial term `a` and common difference `d` is the sum `Σ (i < n) (a + d * i)`

```agda
module _
  {l : Level} (R : Semiring l) (a d : type-Semiring R)
  where

  htpy-sum-standard-arithmetic-sequence-add-mul-nat-Semiring :
    seq-sum-add-mul-nat-Semiring R a d ~
    seq-sum-standard-arithmetic-sequence-Semiring R a d
  htpy-sum-standard-arithmetic-sequence-add-mul-nat-Semiring =
    htpy-seq-sum-sequence-Semiring
      ( R)
      ( htpy-add-mul-standard-arithmetic-sequence-Semiring R a d)
```
