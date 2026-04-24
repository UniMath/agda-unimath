# Partitions of closed intervals of real numbers

```agda
module real-numbers.partitions-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.tuples

open import order-theory.increasing-arrays-posets
open import order-theory.increasing-finite-sequences-posets
open import order-theory.increasing-nonempty-arrays-posets
open import order-theory.large-posets
open import order-theory.least-upper-bounds-large-posets
open import order-theory.lower-bounds-large-posets
open import order-theory.opposite-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.upper-bounds-large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maximum-finite-families-nonnegative-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A
{{#concept "partition" Disambiguation="of a closed interval in ℝ" Agda=partition-closed-interval-ℝ}}
of a [closed interval](real-numbers.closed-intervals-real-numbers.md) `[a, b]`
in the [real numbers](real-numbers.dedekind-real-numbers.md) is an
[increasing nonempty array](order-theory.increasing-nonempty-arrays-posets.md)
in `ℝ` whose first element is `a` and whose last element is `b`.

## Definition

```agda
module _
  {l : Level}
  ([a,b]@((a , b) , a≤b) : closed-interval-ℝ l l)
  where

  partition-closed-interval-ℝ : UU (lsuc l)
  partition-closed-interval-ℝ =
    Σ ( increasing-nonempty-array-type-Poset (ℝ-Poset l))
      ( λ u →
        ( head-increasing-nonempty-array-type-Poset (ℝ-Poset l) u ＝ a) ×
        ( last-increasing-nonempty-array-type-Poset (ℝ-Poset l) u ＝ b))

  pred-length-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ → ℕ
  pred-length-partition-closed-interval-ℝ ((((succ-ℕ n , _) , _) , _) , _) =
    n

  length-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ → ℕ
  length-partition-closed-interval-ℝ =
    succ-ℕ ∘ pred-length-partition-closed-interval-ℝ

  real-fin-sequence-partition-closed-interval-ℝ :
    (p : partition-closed-interval-ℝ) →
    fin-sequence (ℝ l) (length-partition-closed-interval-ℝ p)
  real-fin-sequence-partition-closed-interval-ℝ
    ((((succ-ℕ n , u) , _) , _) , _) = u

  is-increasing-real-fin-sequence-partition-closed-interval-ℝ :
    (p : partition-closed-interval-ℝ) →
    is-increasing-fin-sequence-type-Poset
      ( ℝ-Poset l)
      ( length-partition-closed-interval-ℝ p)
      ( real-fin-sequence-partition-closed-interval-ℝ p)
  is-increasing-real-fin-sequence-partition-closed-interval-ℝ
    ((((succ-ℕ n , u) , _) , H) , _) =
    H

  increasing-real-fin-sequence-partition-closed-interval-ℝ :
    (p : partition-closed-interval-ℝ) →
    increasing-fin-sequence-type-Poset
      ( ℝ-Poset l)
      ( length-partition-closed-interval-ℝ p)
  increasing-real-fin-sequence-partition-closed-interval-ℝ
    ((((succ-ℕ n , u) , _) , H) , _) =
    ( u , H)

  abstract
    reverses-order-fin-sequence-partition-closed-interval-ℝ :
      (p : partition-closed-interval-ℝ) →
      preserves-order-Poset
        ( opposite-Poset (Fin-Poset (length-partition-closed-interval-ℝ p)))
        ( ℝ-Poset l)
        ( real-fin-sequence-partition-closed-interval-ℝ p)
    reverses-order-fin-sequence-partition-closed-interval-ℝ
      ((((succ-ℕ n , u) , _) , H) , _) =
      reverses-order-is-increasing-fin-sequence-type-Poset
        ( ℝ-Poset l)
        ( succ-ℕ n)
        ( u)
        ( H)

  eq-lower-bound-head-real-fin-sequence-partition-closed-interval-ℝ :
    (p : partition-closed-interval-ℝ) →
    head-fin-sequence
      ( pred-length-partition-closed-interval-ℝ p)
      ( real-fin-sequence-partition-closed-interval-ℝ p) ＝
    a
  eq-lower-bound-head-real-fin-sequence-partition-closed-interval-ℝ
    ((((succ-ℕ n , u) , _) , _) , u₋₁=a , _) =
    u₋₁=a

  eq-upper-bound-last-real-fin-sequence-partition-closed-interval-ℝ :
    (p : partition-closed-interval-ℝ) →
    last-fin-sequence
      ( pred-length-partition-closed-interval-ℝ p)
      ( real-fin-sequence-partition-closed-interval-ℝ p) ＝
    b
  eq-upper-bound-last-real-fin-sequence-partition-closed-interval-ℝ
    ((((succ-ℕ n , u) , _) , _) , _ , u₀=b) =
    u₀=b

  abstract
    lower-bound-real-fin-sequence-partition-closed-interval-ℝ :
      (p : partition-closed-interval-ℝ) →
      is-lower-bound-family-of-elements-Large-Poset
        ( ℝ-Large-Poset)
        ( real-fin-sequence-partition-closed-interval-ℝ p)
        ( a)
    lower-bound-real-fin-sequence-partition-closed-interval-ℝ p i =
      binary-tr
        ( leq-ℝ)
        ( eq-lower-bound-head-real-fin-sequence-partition-closed-interval-ℝ p)
        ( refl)
        ( reverses-order-fin-sequence-partition-closed-interval-ℝ
          ( p)
          ( neg-one-Fin (pred-length-partition-closed-interval-ℝ p))
          ( i)
          ( leq-neg-one-Fin (pred-length-partition-closed-interval-ℝ p) i))

    upper-bound-real-fin-sequence-partition-closed-interval-ℝ :
      (p : partition-closed-interval-ℝ) →
      is-upper-bound-family-of-elements-Large-Poset
        ( ℝ-Large-Poset)
        ( real-fin-sequence-partition-closed-interval-ℝ p)
        ( b)
    upper-bound-real-fin-sequence-partition-closed-interval-ℝ p i =
      binary-tr
        ( leq-ℝ)
        ( refl)
        ( eq-upper-bound-last-real-fin-sequence-partition-closed-interval-ℝ p)
        ( reverses-order-fin-sequence-partition-closed-interval-ℝ
          ( p)
          ( i)
          ( zero-Fin (pred-length-partition-closed-interval-ℝ p))
          ( leq-zero-Fin (pred-length-partition-closed-interval-ℝ p) i))

  fin-sequence-partition-closed-interval-ℝ :
    (p : partition-closed-interval-ℝ) →
    fin-sequence
      ( type-closed-interval-ℝ l [a,b])
      ( length-partition-closed-interval-ℝ p)
  fin-sequence-partition-closed-interval-ℝ p i =
    ( real-fin-sequence-partition-closed-interval-ℝ p i ,
      lower-bound-real-fin-sequence-partition-closed-interval-ℝ p i ,
      upper-bound-real-fin-sequence-partition-closed-interval-ℝ p i)
```

## Properties

### The sequence of closed intervals of a partition

```agda
fin-sequence-closed-interval-partition-closed-interval-ℝ :
  {l : Level} ([a,b] : closed-interval-ℝ l l)
  (p : partition-closed-interval-ℝ [a,b]) →
  fin-sequence
    ( closed-interval-ℝ l l)
    ( pred-length-partition-closed-interval-ℝ [a,b] p)
fin-sequence-closed-interval-partition-closed-interval-ℝ {l} [a,b] p =
  closed-intervals-increasing-fin-sequence-type-Poset
    ( ℝ-Poset l)
    ( pred-length-partition-closed-interval-ℝ [a,b] p)
    ( increasing-real-fin-sequence-partition-closed-interval-ℝ [a,b] p)
```

### The mesh of a partition

```agda
module _
  {l : Level}
  ([a,b] : closed-interval-ℝ l l)
  where

  diffs-partition-closed-interval-ℝ :
    (p : partition-closed-interval-ℝ [a,b]) →
    fin-sequence
      ( ℝ⁰⁺ l)
      ( pred-length-partition-closed-interval-ℝ [a,b] p)
  diffs-partition-closed-interval-ℝ p =
    ( nonnegative-width-closed-interval-ℝ) ∘
    ( fin-sequence-closed-interval-partition-closed-interval-ℝ [a,b] p)

  mesh-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ [a,b] → ℝ⁰⁺ l
  mesh-partition-closed-interval-ℝ p =
    max-fin-sequence-ℝ⁰⁺
      ( pred-length-partition-closed-interval-ℝ [a,b] p)
      ( diffs-partition-closed-interval-ℝ p)

  real-mesh-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ [a,b] → ℝ l
  real-mesh-partition-closed-interval-ℝ =
    real-ℝ⁰⁺ ∘ mesh-partition-closed-interval-ℝ
```

### The mesh of a partition of a closed interval is at most the width of the interval

```agda
module _
  {l : Level}
  ([a,b]@((a , b) , a≤b) : closed-interval-ℝ l l)
  where

  abstract
    bound-diffs-partition-closed-interval-ℝ :
      (p : partition-closed-interval-ℝ [a,b]) →
      is-upper-bound-family-of-elements-Large-Poset
        ( large-poset-ℝ⁰⁺)
        ( diffs-partition-closed-interval-ℝ [a,b] p)
        ( nonnegative-width-closed-interval-ℝ [a,b])
    bound-diffs-partition-closed-interval-ℝ
      p@((((succ-ℕ n , u) , _) , _) , _) i =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
          real-ℝ⁰⁺ (diffs-partition-closed-interval-ℝ [a,b] p i)
          ≤ u (inl-Fin n i) -ℝ u (skip-zero-Fin n i)
            by
              leq-eq-ℝ
                ( ap
                  ( width-closed-interval-ℝ)
                  ( htpy-closed-intervals-increasing-fin-sequence-type-Poset'
                    ( ℝ-Poset l)
                    ( pred-length-partition-closed-interval-ℝ [a,b] p)
                    ( increasing-real-fin-sequence-partition-closed-interval-ℝ
                      ( [a,b])
                      ( p))
                    ( i)))
          ≤ b -ℝ u (skip-zero-Fin n i)
            by
              preserves-leq-right-add-ℝ _ _ _
                ( upper-bound-real-fin-sequence-partition-closed-interval-ℝ
                  ( [a,b])
                  ( p)
                  ( inl-Fin n i))
          ≤ b -ℝ a
            by
              reverses-leq-left-diff-ℝ _
                ( lower-bound-real-fin-sequence-partition-closed-interval-ℝ
                  ( [a,b])
                  ( p)
                  ( skip-zero-Fin n i))

    bound-mesh-partition-closed-interval-ℝ :
      (p : partition-closed-interval-ℝ [a,b]) →
      leq-ℝ⁰⁺
        ( mesh-partition-closed-interval-ℝ [a,b] p)
        ( nonnegative-width-closed-interval-ℝ [a,b])
    bound-mesh-partition-closed-interval-ℝ p =
      forward-implication
        ( is-least-upper-bound-max-fin-sequence-ℝ⁰⁺
          ( pred-length-partition-closed-interval-ℝ [a,b] p)
          ( diffs-partition-closed-interval-ℝ [a,b] p)
          ( nonnegative-width-closed-interval-ℝ [a,b]))
        ( bound-diffs-partition-closed-interval-ℝ p)
```

### The trivial partition of a closed interval

```agda
module _
  {l : Level}
  ([a,b]@((a , b) , a≤b) : closed-interval-ℝ l l)
  where

  trivial-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ [a,b]
  trivial-partition-closed-interval-ℝ =
    ( ( ((2 , component-tuple 2 (a ∷ b ∷ empty-tuple)) , star) ,
        a≤b ,
        raise-star) ,
      refl ,
      refl)
```

## External links

- [Partition of an interval](https://en.wikipedia.org/wiki/Partition_of_an_interval)
  on Wikipedia
