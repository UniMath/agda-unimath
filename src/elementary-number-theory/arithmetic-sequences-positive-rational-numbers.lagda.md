# Arithmetic sequences of positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.arithmetic-sequences-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.archimedean-property-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.arithmetic-sequences-semigroups
open import group-theory.powers-of-elements-monoids

open import order-theory.increasing-sequences-posets
open import order-theory.strictly-increasing-sequences-strictly-preordered-sets
open import order-theory.strictly-preordered-sets
```

</details>

## Idea

An
{{#concept "arithmetic sequence" Disambiguation="of positive rational numbers" Agda=arithmetic-sequence-ℚ⁺ WD="arithmetic progression" WDID=Q170008}}
of positive rational numbers is an
[arithmetic sequence](group-theory.arithmetic-sequences-semigroups.md) in the
additive [semigroup](group-theory.semigroups.md) of
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md).

The values of an arithmetic sequence are determined by its initial value and its
common difference; an arithmetic sequence of positive rational numbers is
[strictly increasing](order-theory.strictly-increasing-sequences-strictly-preordered-sets.md).

## Definitions

### Arithmetic sequences of positive rational numbers

```agda
arithmetic-sequence-ℚ⁺ : UU lzero
arithmetic-sequence-ℚ⁺ = arithmetic-sequence-Semigroup semigroup-add-ℚ⁺

module _
  (u : arithmetic-sequence-ℚ⁺)
  where

  seq-arithmetic-sequence-ℚ⁺ : sequence ℚ⁺
  seq-arithmetic-sequence-ℚ⁺ =
    seq-arithmetic-sequence-Semigroup semigroup-add-ℚ⁺ u

  is-arithmetic-seq-arithmetic-sequence-ℚ⁺ :
    is-arithmetic-sequence-Semigroup
      semigroup-add-ℚ⁺
      seq-arithmetic-sequence-ℚ⁺
  is-arithmetic-seq-arithmetic-sequence-ℚ⁺ =
    is-arithmetic-seq-arithmetic-sequence-Semigroup semigroup-add-ℚ⁺ u

  common-difference-arithmetic-sequence-ℚ⁺ : ℚ⁺
  common-difference-arithmetic-sequence-ℚ⁺ =
    common-difference-arithmetic-sequence-Semigroup semigroup-add-ℚ⁺ u

  rational-common-difference-arithmetic-sequence-ℚ⁺ : ℚ
  rational-common-difference-arithmetic-sequence-ℚ⁺ =
    rational-ℚ⁺ common-difference-arithmetic-sequence-ℚ⁺

  is-common-difference-arithmetic-sequence-ℚ⁺ :
    is-common-difference-sequence-Semigroup
      semigroup-add-ℚ⁺
      seq-arithmetic-sequence-ℚ⁺
      common-difference-arithmetic-sequence-ℚ⁺
  is-common-difference-arithmetic-sequence-ℚ⁺ =
    is-common-difference-arithmetic-sequence-Semigroup semigroup-add-ℚ⁺ u

  initial-term-arithmetic-sequence-ℚ⁺ : ℚ⁺
  initial-term-arithmetic-sequence-ℚ⁺ =
    initial-term-arithmetic-sequence-Semigroup semigroup-add-ℚ⁺ u
```

### The standard arithmetic sequence of positive rational numbers with initial term `a` and common difference `d`

```agda
module _
  (a d : ℚ⁺)
  where

  standard-arithmetic-sequence-ℚ⁺ : arithmetic-sequence-ℚ⁺
  standard-arithmetic-sequence-ℚ⁺ =
    standard-arithmetic-sequence-Semigroup semigroup-add-ℚ⁺ a d

  seq-standard-arithmetic-sequence-ℚ⁺ : sequence ℚ⁺
  seq-standard-arithmetic-sequence-ℚ⁺ =
    seq-arithmetic-sequence-ℚ⁺ standard-arithmetic-sequence-ℚ⁺
```

## Properties

### Two arithmetic sequences of positive rational numbers with the same initial term and common difference are homotopic

```agda
htpy-seq-arithmetic-sequence-ℚ⁺ :
  ( u v : arithmetic-sequence-ℚ⁺) →
  ( initial-term-arithmetic-sequence-ℚ⁺ u ＝
    initial-term-arithmetic-sequence-ℚ⁺ v) →
  ( common-difference-arithmetic-sequence-ℚ⁺ u ＝
    common-difference-arithmetic-sequence-ℚ⁺ v) →
  seq-arithmetic-sequence-ℚ⁺ u ~ seq-arithmetic-sequence-ℚ⁺ v
htpy-seq-arithmetic-sequence-ℚ⁺ =
  htpy-seq-arithmetic-sequence-Semigroup semigroup-add-ℚ⁺
```

### The nth term of the arithmetic sequence with initial term `a` and common difference `d` is `a + n * d`

```agda
module _
  (a d : ℚ⁺)
  where

  abstract
    compute-standard-arithmetic-sequence-ℚ⁺ :
      ( n : ℕ) →
      ( rational-ℚ⁺ a +ℚ rational-ℕ n *ℚ rational-ℚ⁺ d) ＝
      ( rational-ℚ⁺ (seq-standard-arithmetic-sequence-ℚ⁺ a d n))
    compute-standard-arithmetic-sequence-ℚ⁺ zero-ℕ =
      ( ap (add-ℚ (rational-ℚ⁺ a)) (left-zero-law-mul-ℚ (rational-ℚ⁺ d))) ∙
      ( right-unit-law-add-ℚ (rational-ℚ⁺ a))
    compute-standard-arithmetic-sequence-ℚ⁺ (succ-ℕ n) =
      ( ap
        ( add-ℚ (rational-ℚ⁺ a))
        ( ( ap (mul-ℚ' (rational-ℚ⁺ d)) (inv (succ-rational-int-ℕ n))) ∙
          ( mul-left-succ-ℚ (rational-ℕ n) (rational-ℚ⁺ d)) ∙
          ( commutative-add-ℚ
            ( rational-ℚ⁺ d)
            ( rational-ℕ n *ℚ rational-ℚ⁺ d)))) ∙
      ( inv
        ( associative-add-ℚ
          ( rational-ℚ⁺ a)
          ( rational-ℕ n *ℚ rational-ℚ⁺ d)
          ( rational-ℚ⁺ d))) ∙
      ( ap
        ( add-ℚ' (rational-ℚ⁺ d))
        ( compute-standard-arithmetic-sequence-ℚ⁺ n))

module _
  (u : arithmetic-sequence-ℚ⁺)
  where

  abstract
    compute-arithmetic-sequence-ℚ⁺ :
      ( n : ℕ) →
      Id
        ( add-ℚ
          ( rational-ℚ⁺ (initial-term-arithmetic-sequence-ℚ⁺ u))
          ( mul-ℚ
            ( rational-ℕ n)
            ( rational-ℚ⁺ (common-difference-arithmetic-sequence-ℚ⁺ u))))
        ( rational-ℚ⁺ (seq-arithmetic-sequence-ℚ⁺ u n))
    compute-arithmetic-sequence-ℚ⁺ n =
      ( compute-standard-arithmetic-sequence-ℚ⁺
        ( initial-term-arithmetic-sequence-ℚ⁺ u)
        ( common-difference-arithmetic-sequence-ℚ⁺ u)
        ( n)) ∙
      ( ap
        ( rational-ℚ⁺)
        ( htpy-seq-standard-arithmetic-sequence-Semigroup
          semigroup-add-ℚ⁺
          u
          n))
```

### An arithmetic sequence of positive rational numbers is strictly increasing

```agda
module _
  (u : arithmetic-sequence-ℚ⁺)
  where

  abstract
    le-succ-seq-arithmetic-sequence-ℚ⁺ :
      (n : ℕ) →
      le-ℚ⁺
        ( seq-arithmetic-sequence-ℚ⁺ u n)
        ( seq-arithmetic-sequence-ℚ⁺ u (succ-ℕ n))
    le-succ-seq-arithmetic-sequence-ℚ⁺ n =
      inv-tr
        ( le-ℚ⁺ (seq-arithmetic-sequence-ℚ⁺ u n))
        ( is-common-difference-arithmetic-sequence-ℚ⁺ u n)
        ( le-right-add-rational-ℚ⁺
          ( rational-ℚ⁺ (seq-arithmetic-sequence-ℚ⁺ u n))
          ( common-difference-arithmetic-sequence-ℚ⁺ u))

    is-strictly-increasing-seq-arithmetic-sequence-ℚ⁺ :
      is-strictly-increasing-sequence-Strictly-Preordered-Set
        ( strictly-preordered-set-ℚ⁺)
        ( seq-arithmetic-sequence-ℚ⁺ u)
    is-strictly-increasing-seq-arithmetic-sequence-ℚ⁺ =
      is-strictly-increasing-le-succ-sequence-Strictly-Preordered-Set
        ( strictly-preordered-set-ℚ⁺)
        ( seq-arithmetic-sequence-ℚ⁺ u)
        ( le-succ-seq-arithmetic-sequence-ℚ⁺)
```

### An arithmetic sequence of positive rational numbers is increasing

```agda
module _
  (u : arithmetic-sequence-ℚ⁺)
  where

  abstract
    leq-succ-seq-arithmetic-sequence-ℚ⁺ :
      (n : ℕ) →
      leq-ℚ⁺
        ( seq-arithmetic-sequence-ℚ⁺ u n)
        ( seq-arithmetic-sequence-ℚ⁺ u (succ-ℕ n))
    leq-succ-seq-arithmetic-sequence-ℚ⁺ n =
      leq-le-ℚ⁺
        { seq-arithmetic-sequence-ℚ⁺ u n}
        { seq-arithmetic-sequence-ℚ⁺ u (succ-ℕ n)}
        ( le-succ-seq-arithmetic-sequence-ℚ⁺ u n)

    is-increasing-seq-arithmetic-sequence-ℚ⁺ :
      is-increasing-sequence-Poset
        ( poset-ℚ⁺)
        ( seq-arithmetic-sequence-ℚ⁺ u)
    is-increasing-seq-arithmetic-sequence-ℚ⁺ =
      is-increasing-leq-succ-sequence-Poset
        ( poset-ℚ⁺)
        ( seq-arithmetic-sequence-ℚ⁺ u)
        ( leq-succ-seq-arithmetic-sequence-ℚ⁺)
```

### The terms of an arithmetic sequence of positive rational numbers are greater than or equal to its initial term

```agda
module _
  (u : arithmetic-sequence-ℚ⁺)
  where

  abstract
    leq-initial-arithmetic-sequence-ℚ⁺ :
      (n : ℕ) →
      leq-ℚ⁺
        ( initial-term-arithmetic-sequence-ℚ⁺ u)
        ( seq-arithmetic-sequence-ℚ⁺ u n)
    leq-initial-arithmetic-sequence-ℚ⁺ zero-ℕ =
      refl-leq-ℚ (rational-ℚ⁺ (initial-term-arithmetic-sequence-ℚ⁺ u))
    leq-initial-arithmetic-sequence-ℚ⁺ (succ-ℕ n) =
      leq-le-ℚ⁺
      { initial-term-arithmetic-sequence-ℚ⁺ u}
      { seq-arithmetic-sequence-ℚ⁺ u (succ-ℕ n)}
      ( concatenate-leq-le-ℚ
        ( rational-ℚ⁺ (initial-term-arithmetic-sequence-ℚ⁺ u))
        ( rational-ℚ⁺ (seq-arithmetic-sequence-ℚ⁺ u n))
        ( rational-ℚ⁺ (seq-arithmetic-sequence-ℚ⁺ u (succ-ℕ n)))
        ( leq-initial-arithmetic-sequence-ℚ⁺ n)
        ( le-succ-seq-arithmetic-sequence-ℚ⁺ u n))
```

## See also

- [Geometric sequences in ℚ⁺](elementary-number-theory.geometric-sequences-positive-rational-numbers.md):
  arithmetic sequences in the **multiplicative** semigroup of ℚ⁺;
- [Bernoulli's inequality in ℚ⁺](elementary-number-theory.bernoullis-inequality-positive-rational-numbers.md):
  comparison between arithmetic and geometric sequences in ℚ⁺.

## External links

- [Arithmetic progressions](https://en.wikipedia.org/wiki/Arithmetic_progression)
  at Wikipedia
