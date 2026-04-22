# Sums of finite sequences of elements of vector spaces

```agda
module linear-algebra.sums-of-finite-sequences-of-elements-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.function-vector-spaces
open import linear-algebra.linear-maps-vector-spaces
open import linear-algebra.sums-of-finite-sequences-of-elements-left-modules-rings
open import linear-algebra.vector-spaces

open import lists.finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence in a vector space" Agda=sum-fin-sequence-type-Vector-Space}}
extends the binary addition operation on a
[vector space](linear-algebra.vector-spaces.md) `V` to any
[finite sequence](lists.finite-sequences.md) of elements of `V`.

## Definition

```agda
sum-fin-sequence-type-Vector-Space :
  {l1 l2 : Level} (K : Heyting-Field l1) (V : Vector-Space l2 K) →
  (n : ℕ) → fin-sequence (type-Vector-Space K V) n → type-Vector-Space K V
sum-fin-sequence-type-Vector-Space K V =
  sum-fin-sequence-type-left-module-Ring (ring-Heyting-Field K) V
```

## Properties

### Sums are homotopy invariant

```agda
module _
  {l1 l2 : Level}
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  where

  abstract
    htpy-sum-fin-sequence-type-Vector-Space :
      (n : ℕ) {f g : fin-sequence (type-Vector-Space K V) n} → f ~ g →
      sum-fin-sequence-type-Vector-Space K V n f ＝
      sum-fin-sequence-type-Vector-Space K V n g
    htpy-sum-fin-sequence-type-Vector-Space =
      htpy-sum-fin-sequence-type-left-module-Ring (ring-Heyting-Field K) V
```

### The distributive law of scalar multiplication over sums

```agda
module _
  {l1 l2 : Level}
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  where

  abstract
    left-distributive-mul-sum-fin-sequence-type-Vector-Space :
      (n : ℕ) (c : type-Heyting-Field K)
      (u : fin-sequence (type-Vector-Space K V) n) →
      mul-Vector-Space K V c (sum-fin-sequence-type-Vector-Space K V n u) ＝
      sum-fin-sequence-type-Vector-Space K V n (mul-Vector-Space K V c ∘ u)
    left-distributive-mul-sum-fin-sequence-type-Vector-Space =
      left-distributive-mul-sum-fin-sequence-type-left-module-Ring
        ( ring-Heyting-Field K)
        ( V)
```

### The distributive law of sums over addition

```agda
module _
  {l1 l2 : Level}
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  where

  abstract
    distributive-sum-add-fin-sequence-type-Vector-Space :
      (n : ℕ) (f g : fin-sequence (type-Vector-Space K V) n) →
      sum-fin-sequence-type-Vector-Space K V
        ( n)
        ( λ i → add-Vector-Space K V (f i) (g i)) ＝
      add-Vector-Space K V
        ( sum-fin-sequence-type-Vector-Space K V n f)
        ( sum-fin-sequence-type-Vector-Space K V n g)
    distributive-sum-add-fin-sequence-type-Vector-Space =
      distributive-sum-add-fin-sequence-type-left-module-Ring
        ( ring-Heyting-Field K)
        ( V)
```

### Permutations preserve sums

```agda
module _
  {l1 l2 : Level}
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  where

  abstract
    preserves-sum-permutation-fin-sequence-type-Vector-Space :
      (n : ℕ) (σ : Permutation n) (u : fin-sequence (type-Vector-Space K V) n) →
      sum-fin-sequence-type-Vector-Space K V n u ＝
      sum-fin-sequence-type-Vector-Space K V n (u ∘ map-equiv σ)
    preserves-sum-permutation-fin-sequence-type-Vector-Space =
      preserves-sum-permutation-fin-sequence-type-left-module-Ring
        ( ring-Heyting-Field K)
        ( V)
```

### The sum operation is a linear map

```agda
module _
  {l1 l2 : Level}
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  (n : ℕ)
  where

  is-linear-map-sum-fin-sequence-type-Vector-Space :
    is-linear-map-Vector-Space
      ( K)
      ( function-Vector-Space K V (Fin n))
      ( V)
      ( sum-fin-sequence-type-Vector-Space K V n)
  is-linear-map-sum-fin-sequence-type-Vector-Space =
    is-linear-map-sum-fin-sequence-type-left-module-Ring
      ( ring-Heyting-Field K)
      ( V)
      ( n)

  linear-map-sum-fin-sequence-type-Vector-Space :
    linear-map-Vector-Space
      ( K)
      ( function-Vector-Space K V (Fin n))
      ( V)
  linear-map-sum-fin-sequence-type-Vector-Space =
    ( sum-fin-sequence-type-Vector-Space K V n ,
      is-linear-map-sum-fin-sequence-type-Vector-Space)
```
