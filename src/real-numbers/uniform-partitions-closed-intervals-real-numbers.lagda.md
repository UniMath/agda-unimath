# Uniform partitions of closed intervals in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniform-partitions-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.null-homotopic-maps
open import foundation.subtypes
open import foundation.universe-levels
open import foundation.weakly-constant-maps

open import lists.finite-sequences

open import order-theory.least-upper-bounds-large-posets
open import order-theory.similarity-of-elements-large-posets

open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.maximum-finite-families-nonnegative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.partitions-closed-intervals-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A {{#concept "uniform partition" Agda=uniform-partition-closed-interval-ℝ}} of a
[closed interval](real-numbers.closed-intervals-real-numbers.md) `[a, b]` in the
[real numbers](real-numbers.dedekind-real-numbers.md) is a
[partition](real-numbers.partitions-closed-intervals-real-numbers.md) in which
the widths of the component intervals are
[weakly constant](foundation.weakly-constant-maps.md).

## Definition

```agda
module _
  {l : Level}
  ([a,b] : closed-interval-ℝ l l)
  where

  is-uniform-prop-partition-closed-interval-ℝ :
    subtype (lsuc l) (partition-closed-interval-ℝ [a,b])
  is-uniform-prop-partition-closed-interval-ℝ p =
    is-weakly-constant-map-prop-Set
      ( ℝ-Set l)
      ( width-closed-interval-ℝ ∘
        fin-sequence-closed-interval-partition-closed-interval-ℝ [a,b] p)

  is-uniform-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ [a,b] → UU (lsuc l)
  is-uniform-partition-closed-interval-ℝ =
    is-in-subtype is-uniform-prop-partition-closed-interval-ℝ

  uniform-partition-closed-interval-ℝ : UU (lsuc l)
  uniform-partition-closed-interval-ℝ =
    type-subtype is-uniform-prop-partition-closed-interval-ℝ
```

## Properties

### Properties inherited from all partitions

```agda
module _
  {l : Level}
  ([a,b] : closed-interval-ℝ l l)
  (up@(p , is-uniform-p) :
    uniform-partition-closed-interval-ℝ [a,b])
  where

  partition-uniform-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ [a,b]
  partition-uniform-partition-closed-interval-ℝ = p

  pred-length-uniform-partition-closed-interval-ℝ : ℕ
  pred-length-uniform-partition-closed-interval-ℝ =
    pred-length-partition-closed-interval-ℝ [a,b] p

  length-uniform-partition-closed-interval-ℝ : ℕ
  length-uniform-partition-closed-interval-ℝ =
    length-partition-closed-interval-ℝ [a,b] p

  fin-sequence-closed-interval-uniform-partition-closed-interval-ℝ :
    fin-sequence
      ( closed-interval-ℝ l l)
      ( pred-length-uniform-partition-closed-interval-ℝ)
  fin-sequence-closed-interval-uniform-partition-closed-interval-ℝ =
    fin-sequence-closed-interval-partition-closed-interval-ℝ [a,b] p

  fin-sequence-nonnegative-width-closed-interval-uniform-partition-closed-interval-ℝ :
    fin-sequence (ℝ⁰⁺ l) (pred-length-uniform-partition-closed-interval-ℝ)
  fin-sequence-nonnegative-width-closed-interval-uniform-partition-closed-interval-ℝ =
    nonnegative-width-closed-interval-ℝ ∘
    fin-sequence-closed-interval-uniform-partition-closed-interval-ℝ

  abstract
    is-weakly-constant-fin-sequence-nonnegative-width-closed-interval-uniform-partition-closed-interval-ℝ :
      is-weakly-constant-map
        ( fin-sequence-nonnegative-width-closed-interval-uniform-partition-closed-interval-ℝ)
    is-weakly-constant-fin-sequence-nonnegative-width-closed-interval-uniform-partition-closed-interval-ℝ
      i j =
      eq-ℝ⁰⁺ _ _ (is-uniform-p i j)
```

### The width of partitions in a uniform partition

If the partition is trivial, containing no partitions because it is a partition
of a singleton interval `[a, a]`, we define the width of the partitions to be
zero.

```agda
module _
  {l : Level}
  ([a,b] : closed-interval-ℝ l l)
  (up@(p , is-uniform-p) :
    uniform-partition-closed-interval-ℝ [a,b])
  where

  mesh-uniform-partition-closed-interval-ℝ : ℝ⁰⁺ l
  mesh-uniform-partition-closed-interval-ℝ =
    mesh-partition-closed-interval-ℝ [a,b] p

  real-mesh-interval-uniform-partition-closed-interval-ℝ : ℝ l
  real-mesh-interval-uniform-partition-closed-interval-ℝ =
    real-ℝ⁰⁺ mesh-uniform-partition-closed-interval-ℝ

  is-null-homotopic-fin-sequence-nonnegative-width-closed-interval-uniform-partition-closed-interval-ℝ :
    is-null-homotopic-map
      ( fin-sequence-nonnegative-width-closed-interval-uniform-partition-closed-interval-ℝ
        ( [a,b])
        ( up))
  pr1
    is-null-homotopic-fin-sequence-nonnegative-width-closed-interval-uniform-partition-closed-interval-ℝ =
    mesh-uniform-partition-closed-interval-ℝ
  pr2
    is-null-homotopic-fin-sequence-nonnegative-width-closed-interval-uniform-partition-closed-interval-ℝ
    i =
    inv
      ( max-weakly-constant-fin-sequence-ℝ⁰⁺
        ( pred-length-uniform-partition-closed-interval-ℝ [a,b] up)
        ( diffs-partition-closed-interval-ℝ [a,b] p)
        ( is-weakly-constant-fin-sequence-nonnegative-width-closed-interval-uniform-partition-closed-interval-ℝ
          ( [a,b])
          ( up))
        ( i))
```
