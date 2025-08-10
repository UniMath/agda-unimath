# The sum of terms of an arithmetic sequences in a semiring

```agda
module ring-theory.sum-of-terms-arithmetic-sequences-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.sets
open import foundation.universe-levels

open import group-theory.arithmetic-sequences-semigroups

open import lists.finite-sequences

open import ring-theory.arithmetic-sequences-semirings
open import ring-theory.semirings
open import ring-theory.series-semirings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings
```

</details>

## Ideas

The
{{#concept "sum of initial terms of an arithmetic sequence" Agda=seq-sum-arithmetic-sequence-Semiring}}
in a [semiring](ring-theory.semirings.md) is the
[sequence](foundation.sequences.md) defined by

```text
n ↦ Σ (k < n) (u k)
```

for some [arithmetic sequence](ring-theory.arithmetic-sequences-semirings.md) in
the semiring.

## Definitions

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
