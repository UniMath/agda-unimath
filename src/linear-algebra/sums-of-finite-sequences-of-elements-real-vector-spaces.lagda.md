# Sums of finite sequences of elements of real vector spaces

```agda
module linear-algebra.sums-of-finite-sequences-of-elements-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.function-real-vector-spaces
open import linear-algebra.linear-maps-real-vector-spaces
open import linear-algebra.real-vector-spaces
open import linear-algebra.sums-of-finite-sequences-of-elements-vector-spaces

open import lists.finite-sequences

open import real-numbers.dedekind-real-numbers
open import real-numbers.field-of-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence in a real vector space" Agda=sum-fin-sequence-type-ℝ-Vector-Space}}
extends the binary addition operation on a
[real vector space](linear-algebra.real-vector-spaces.md) `V` to any
[finite sequence](lists.finite-sequences.md) of elements of `V`.

## Definition

```agda
sum-fin-sequence-type-ℝ-Vector-Space :
  {l1 l2 : Level} (V : ℝ-Vector-Space l1 l2) →
  (n : ℕ) → fin-sequence (type-ℝ-Vector-Space V) n → type-ℝ-Vector-Space V
sum-fin-sequence-type-ℝ-Vector-Space {l1 = l1} =
  sum-fin-sequence-type-Vector-Space (heyting-field-ℝ l1)
```

## Properties

### Homotopic sequences have the same sum

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  where

  abstract
    htpy-sum-fin-sequence-type-ℝ-Vector-Space :
      (n : ℕ) {f g : fin-sequence (type-ℝ-Vector-Space V) n} → f ~ g →
      sum-fin-sequence-type-ℝ-Vector-Space V n f ＝
      sum-fin-sequence-type-ℝ-Vector-Space V n g
    htpy-sum-fin-sequence-type-ℝ-Vector-Space =
      htpy-sum-fin-sequence-type-Vector-Space (heyting-field-ℝ l1) V
```

### Permutations preserve sums

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  where

  abstract
    preserves-sum-permutation-fin-sequence-type-ℝ-Vector-Space :
      (n : ℕ) (σ : Permutation n) (u : fin-sequence (type-ℝ-Vector-Space V) n) →
      sum-fin-sequence-type-ℝ-Vector-Space V n u ＝
      sum-fin-sequence-type-ℝ-Vector-Space V n (u ∘ map-equiv σ)
    preserves-sum-permutation-fin-sequence-type-ℝ-Vector-Space =
      preserves-sum-permutation-fin-sequence-type-Vector-Space
        ( heyting-field-ℝ l1)
        ( V)
```

### Scalar multiplication distributes over sums

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  where

  abstract
    left-distributive-mul-sum-fin-sequence-type-ℝ-Vector-Space :
      (n : ℕ) (c : ℝ l1) (u : fin-sequence (type-ℝ-Vector-Space V) n) →
      mul-ℝ-Vector-Space V c (sum-fin-sequence-type-ℝ-Vector-Space V n u) ＝
      sum-fin-sequence-type-ℝ-Vector-Space V n (mul-ℝ-Vector-Space V c ∘ u)
    left-distributive-mul-sum-fin-sequence-type-ℝ-Vector-Space =
      left-distributive-mul-sum-fin-sequence-type-Vector-Space
        ( heyting-field-ℝ l1)
        ( V)
```

### Distributive law of sums and addition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  where

  abstract
    interchange-sum-add-fin-sequence-type-ℝ-Vector-Space :
      (n : ℕ) (f g : fin-sequence (type-ℝ-Vector-Space V) n) →
      sum-fin-sequence-type-ℝ-Vector-Space V
        ( n)
        ( λ i → add-ℝ-Vector-Space V (f i) (g i)) ＝
      add-ℝ-Vector-Space V
        ( sum-fin-sequence-type-ℝ-Vector-Space V n f)
        ( sum-fin-sequence-type-ℝ-Vector-Space V n g)
    interchange-sum-add-fin-sequence-type-ℝ-Vector-Space =
      interchange-sum-add-fin-sequence-type-Vector-Space (heyting-field-ℝ l1) V
```

### Sums distribute over differences

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  where

  abstract
    interchange-sum-diff-fin-sequence-type-ℝ-Vector-Space :
      (n : ℕ) (f g : fin-sequence (type-ℝ-Vector-Space V) n) →
      sum-fin-sequence-type-ℝ-Vector-Space V
        ( n)
        ( λ i → diff-ℝ-Vector-Space V (f i) (g i)) ＝
      diff-ℝ-Vector-Space V
        ( sum-fin-sequence-type-ℝ-Vector-Space V n f)
        ( sum-fin-sequence-type-ℝ-Vector-Space V n g)
    interchange-sum-diff-fin-sequence-type-ℝ-Vector-Space =
      interchange-sum-diff-fin-sequence-type-Vector-Space
        ( heyting-field-ℝ l1)
        ( V)
```

### Negation distributes over sums

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  where

  abstract
    distributive-neg-sum-fin-sequence-type-ℝ-Vector-Space :
      (n : ℕ) (u : fin-sequence (type-ℝ-Vector-Space V) n) →
      neg-ℝ-Vector-Space V (sum-fin-sequence-type-ℝ-Vector-Space V n u) ＝
      sum-fin-sequence-type-ℝ-Vector-Space V n (neg-ℝ-Vector-Space V ∘ u)
    distributive-neg-sum-fin-sequence-type-ℝ-Vector-Space =
      distributive-neg-sum-fin-sequence-type-Vector-Space
        ( heyting-field-ℝ l1)
        ( V)
```

### The sum operation is a linear map

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  (n : ℕ)
  where

  is-linear-map-sum-fin-sequence-type-ℝ-Vector-Space :
    is-linear-map-ℝ-Vector-Space
      ( function-ℝ-Vector-Space V (Fin n))
      ( V)
      ( sum-fin-sequence-type-ℝ-Vector-Space V n)
  is-linear-map-sum-fin-sequence-type-ℝ-Vector-Space =
    is-linear-map-sum-fin-sequence-type-Vector-Space (heyting-field-ℝ l1) V n

  linear-map-sum-fin-sequence-type-ℝ-Vector-Space :
    linear-map-ℝ-Vector-Space
      ( function-ℝ-Vector-Space V (Fin n))
      ( V)
  linear-map-sum-fin-sequence-type-ℝ-Vector-Space =
    ( sum-fin-sequence-type-ℝ-Vector-Space V n ,
      is-linear-map-sum-fin-sequence-type-ℝ-Vector-Space)
```
