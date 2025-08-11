# Arithmetic series in semirings

```agda
module ring-theory.arithmetic-series-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.commutative-semiring-of-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.triangular-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import lists.finite-sequences

open import ring-theory.arithmetic-sequences-semirings
open import ring-theory.partial-sums-sequences-semirings
open import ring-theory.semirings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings
```

</details>

## Ideas

An
{{#concept "arithmetic series" Disambiguation="in a semiring" Agda=seq-sum-arithmetic-sequence-Semiring}}
in a [semiring](ring-theory.semirings.md) is the
[sequence](foundation.sequences.md) of
[partial sums](ring-theory.partial-sums-sequences-semirings.md)

```text
n ↦ Σ (k ≤ n) (u k)
```

of some [arithmetic sequence](ring-theory.arithmetic-sequences-semirings.md) `u`
in the semiring. These are the sums

```text
n ↦ Σ (k ≤ n) (a + k * d) = (n + 1) * a + Tₙ * d
```

for some elements `a d : R` in the semiring, where `Tₙ` is the nth
[triangular number](elementary-number-theory.triangular-numbers.md).

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

### The sums `Σ (i ≤ n) (a + i * d)`

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

### The nth partial sum of terms of the standard arithmetic sequence with initial term `a` and common difference `d` is the sum `Σ (i ≤ n) (a + i * d)`

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

### The sum `Σ (i ≤ n) (a + i * d)` is equal to `(n + 1) * a + Tₙ * d` where `Tₙ` is the nth triangular number

```agda
module _
  {l : Level} (R : Semiring l) (a d : type-Semiring R)
  where

  compute-sum-add-mul-nat-Semiring :
    (n : ℕ) →
    add-Semiring
      ( R)
      ( mul-nat-scalar-Semiring R (succ-ℕ n) a)
      ( mul-nat-scalar-Semiring
        ( R)
        ( triangular-number-ℕ n)
        ( d)) ＝
    seq-sum-add-mul-nat-Semiring R a d n
  compute-sum-add-mul-nat-Semiring n =
    ap-binary
      ( add-Semiring R)
      ( inv (eq-mul-nat-scalar-sum-const-fin-sequence-Semiring R a (succ-ℕ n)))
      ( ( ap
          ( λ i → mul-nat-scalar-Semiring R i d)
          ( inv (htpy-sum-fin-triangular-number-ℕ n))) ∙
        ( lemma-mul-nat-seq-sum)) ∙
    ( interchange-add-sum-fin-sequence-type-Semiring
      ( R)
      ( succ-ℕ n)
      ( fin-sequence-sequence (λ _ → a) (succ-ℕ n))
      ( fin-sequence-sequence
        ( λ k → mul-nat-scalar-Semiring R k d)
        ( succ-ℕ n)))
    where

    lemma-seq-sum-mul-nat :
      ( seq-sum-sequence-Semiring
        ( R)
        ( λ i → mul-nat-scalar-Semiring R i d)
        ( n)) ＝
      ( mul-Semiring
        ( R)
        ( seq-sum-sequence-Semiring
          ( R)
          ( map-nat-Semiring R)
          ( n))
        ( d))
    lemma-seq-sum-mul-nat =
      inv
        ( ( right-distributive-mul-sum-fin-sequence-type-Semiring
            ( R)
            ( succ-ℕ n)
            ( fin-sequence-sequence
              ( map-nat-Semiring R)
              ( succ-ℕ n))
              ( d)) ∙
          ( htpy-seq-sum-sequence-Semiring
            ( R)
            ( λ i → htpy-mul-map-mul-nat-scalar-Semiring R i d)
            ( n)))

    lemma-seq-sum-map-nat :
      ( k : ℕ) →
      ( seq-sum-sequence-Semiring R (map-nat-Semiring R) k) ＝
      ( map-nat-Semiring
        ( R)
        ( seq-sum-sequence-Semiring
          ( ℕ-Semiring)
          ( λ i → i)
          ( k)))
    lemma-seq-sum-map-nat zero-ℕ =
      compute-sum-one-element-Semiring
        ( R)
        ( λ _ → zero-Semiring R) ∙
        ( inv (left-zero-law-mul-nat-scalar-Semiring R (one-Semiring R)))
    lemma-seq-sum-map-nat (succ-ℕ k) =
      ap-binary
        ( add-Semiring R)
        ( lemma-seq-sum-map-nat k)
        ( inv (eq-fin-sequence-sequence (map-nat-Semiring R) (succ-ℕ k))) ∙
      inv
        ( right-distributive-mul-nat-scalar-add-Semiring
          ( R)
          ( seq-sum-sequence-Semiring ℕ-Semiring (λ i → i) k)
          ( succ-ℕ k)
          ( one-Semiring R))

    lemma-mul-nat-seq-sum :
      mul-nat-scalar-Semiring
        ( R)
        ( seq-sum-sequence-Semiring
          ( ℕ-Semiring)
          ( λ k → k)
          ( n))
        ( d) ＝
      sum-fin-sequence-type-Semiring
        ( R)
        ( succ-ℕ n)
        ( fin-sequence-sequence
          ( λ k → mul-nat-scalar-Semiring R k d)
          ( succ-ℕ n))
    lemma-mul-nat-seq-sum =
      ( inv
        ( htpy-mul-map-mul-nat-scalar-Semiring
          ( R)
          ( seq-sum-sequence-Semiring
            ( ℕ-Semiring)
            ( λ k → k)
            ( n))
          ( d))) ∙
      ( ap
        ( mul-Semiring' R d)
        ( inv (lemma-seq-sum-map-nat n))) ∙
      ( inv lemma-seq-sum-mul-nat)
```
