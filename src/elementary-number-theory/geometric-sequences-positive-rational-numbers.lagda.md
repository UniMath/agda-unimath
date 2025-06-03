# Geometric sequences of positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.geometric-sequences-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.arithmetic-sequences-positive-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.arithmetic-sequences-semigroups
open import group-theory.powers-of-elements-monoids

open import order-theory.strictly-increasing-sequences-strictly-preordered-sets
```

</details>

## Idea

A
{{#concept "geometric sequence" Disambiguation="of positive rational numbers" Agda=geometric-sequence-ℚ⁺ WD="geometric progression" WDID=Q173523}}
of
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
is an [arithmetic sequence](group-theory.arithmetic-sequences-semigroups.md) in
the multiplicative semigroup of positive rational numbers. The multiplicative
common difference in `ℚ⁺` is called the _common ratio_ of the sequence.

Constant sequences are the geometric sequences with common ratio equal to `1`.
The product of two geometric sequences is geometric and the
[inverse](elementary-number-theory.multiplicative-group-of-positive-rational-numbers.md)
of a geometric sequence is geometric; moreover the map from a sequence to its
common ratio commutes with multiplication and inversion.

## Definitions

### Geometric sequences of positive rational numbers

```agda
is-common-ratio-sequence-ℚ⁺ : sequence ℚ⁺ → ℚ⁺ → UU lzero
is-common-ratio-sequence-ℚ⁺ =
  is-common-difference-sequence-Semigroup semigroup-mul-ℚ⁺

is-geometric-sequence-ℚ⁺ : sequence ℚ⁺ → UU lzero
is-geometric-sequence-ℚ⁺ =
  is-arithmetic-sequence-Semigroup semigroup-mul-ℚ⁺

geometric-sequence-ℚ⁺ : UU lzero
geometric-sequence-ℚ⁺ = arithmetic-sequence-Semigroup semigroup-mul-ℚ⁺

module _
  (u : geometric-sequence-ℚ⁺)
  where

  seq-geometric-sequence-ℚ⁺ : sequence ℚ⁺
  seq-geometric-sequence-ℚ⁺ =
    seq-arithmetic-sequence-Semigroup semigroup-mul-ℚ⁺ u

  is-geometric-seq-geometric-sequence-ℚ⁺ :
    is-geometric-sequence-ℚ⁺
      seq-geometric-sequence-ℚ⁺
  is-geometric-seq-geometric-sequence-ℚ⁺ =
    is-arithmetic-seq-arithmetic-sequence-Semigroup
      semigroup-mul-ℚ⁺
      u

  common-ratio-geometric-sequence-ℚ⁺ : ℚ⁺
  common-ratio-geometric-sequence-ℚ⁺ =
    common-difference-arithmetic-sequence-Semigroup
      semigroup-mul-ℚ⁺
      u

  is-common-ratio-geometric-sequence-ℚ⁺ :
    ( n : ℕ) →
    ( seq-geometric-sequence-ℚ⁺ (succ-ℕ n)) ＝
    ( seq-geometric-sequence-ℚ⁺ n *ℚ⁺ common-ratio-geometric-sequence-ℚ⁺)
  is-common-ratio-geometric-sequence-ℚ⁺ =
    is-common-difference-arithmetic-sequence-Semigroup
      semigroup-mul-ℚ⁺
      u

  initial-term-geometric-sequence-ℚ⁺ : ℚ⁺
  initial-term-geometric-sequence-ℚ⁺ =
    initial-term-arithmetic-sequence-Semigroup
      semigroup-mul-ℚ⁺
      u
```

### The standard geometric sequence of positive rational numbers with initial term `a` and common ratio `r`

```agda
module _
  (a r : ℚ⁺)
  where

  standard-geometric-sequence-ℚ⁺ : geometric-sequence-ℚ⁺
  standard-geometric-sequence-ℚ⁺ =
    standard-arithmetic-sequence-Semigroup semigroup-mul-ℚ⁺ a r

  seq-standard-geometric-sequence-ℚ⁺ : sequence ℚ⁺
  seq-standard-geometric-sequence-ℚ⁺ =
    seq-geometric-sequence-ℚ⁺ standard-geometric-sequence-ℚ⁺
```

## Properties

### Two geometric sequences with the same initial term and the same common ratio are homotopic

```agda
htpy-seq-geometric-sequence-ℚ⁺ :
  ( u v : geometric-sequence-ℚ⁺) →
  ( initial-term-geometric-sequence-ℚ⁺ u ＝
    initial-term-geometric-sequence-ℚ⁺ v) →
  ( common-ratio-geometric-sequence-ℚ⁺ u ＝
    common-ratio-geometric-sequence-ℚ⁺ v) →
  seq-geometric-sequence-ℚ⁺ u ~
  seq-geometric-sequence-ℚ⁺ v
htpy-seq-geometric-sequence-ℚ⁺ =
  htpy-seq-arithmetic-sequence-Semigroup semigroup-mul-ℚ⁺
```

### Any geometric sequence of positive rational numbers is standard

```agda
htpy-seq-standard-geometric-sequence-ℚ⁺ :
  ( u : geometric-sequence-ℚ⁺) →
  ( seq-standard-geometric-sequence-ℚ⁺
    ( initial-term-geometric-sequence-ℚ⁺ u)
    ( common-ratio-geometric-sequence-ℚ⁺ u)) ~
  ( seq-geometric-sequence-ℚ⁺ u)
htpy-seq-standard-geometric-sequence-ℚ⁺ =
  htpy-seq-standard-arithmetic-sequence-Semigroup semigroup-mul-ℚ⁺
```

### The nth term of a geometric sequence with initial term `a` and common ratio `r` is `a rⁿ`

```agda
module _
  (a r : ℚ⁺)
  where

  abstract
    compute-standard-geometric-sequence-ℚ⁺ :
      ( n : ℕ) →
      ( a *ℚ⁺ power-Monoid monoid-mul-ℚ⁺ n r) ＝
      ( seq-standard-geometric-sequence-ℚ⁺ a r n)
    compute-standard-geometric-sequence-ℚ⁺ zero-ℕ =
      right-unit-law-mul-ℚ⁺ a
    compute-standard-geometric-sequence-ℚ⁺ (succ-ℕ n) =
      ( ap
        ( mul-ℚ⁺ a)
        ( power-succ-Monoid monoid-mul-ℚ⁺ n r)) ∙
      ( inv
        ( associative-mul-ℚ⁺
          ( a)
          ( power-Monoid monoid-mul-ℚ⁺ n r)
          ( r))) ∙
      ( ap (λ p → p *ℚ⁺ r) (compute-standard-geometric-sequence-ℚ⁺ n))

module _
  (u : geometric-sequence-ℚ⁺)
  where

  abstract
    compute-geometric-sequence-ℚ⁺ :
      (n : ℕ) →
      Id
        ( mul-ℚ⁺
          ( initial-term-geometric-sequence-ℚ⁺ u)
          ( power-Monoid monoid-mul-ℚ⁺
            ( n)
            ( common-ratio-geometric-sequence-ℚ⁺ u)))
        ( seq-geometric-sequence-ℚ⁺ u n)
    compute-geometric-sequence-ℚ⁺ n =
      ( compute-standard-geometric-sequence-ℚ⁺
        ( initial-term-geometric-sequence-ℚ⁺ u)
        ( common-ratio-geometric-sequence-ℚ⁺ u)
        ( n)) ∙
      ( htpy-seq-standard-geometric-sequence-ℚ⁺ u n)
```

### A constant sequence of positive rational numbers is geometric with common ratio equal to `1`

```agda
module _
  (a : ℚ⁺)
  where

  is-geometric-const-sequence-ℚ⁺ : is-geometric-sequence-ℚ⁺ (const ℕ a)
  is-geometric-const-sequence-ℚ⁺ =
    ( one-ℚ⁺ , λ _ → inv (right-unit-law-mul-ℚ⁺ a))

  const-geometric-sequence-ℚ⁺ : geometric-sequence-ℚ⁺
  const-geometric-sequence-ℚ⁺ =
    ( const ℕ a , is-geometric-const-sequence-ℚ⁺)
```

### A geometric sequence of positive rational numbers with common ratio equal to `1` is constant

```agda
module _
  (u : geometric-sequence-ℚ⁺)
  (is-one-common-ratio : common-ratio-geometric-sequence-ℚ⁺ u ＝ one-ℚ⁺)
  where

  is-constant-seq-geometric-sequence-ℚ⁺ :
    (n : ℕ) →
    ( seq-geometric-sequence-ℚ⁺ u n) ＝
    ( initial-term-geometric-sequence-ℚ⁺ u)
  is-constant-seq-geometric-sequence-ℚ⁺ zero-ℕ = refl
  is-constant-seq-geometric-sequence-ℚ⁺ (succ-ℕ n) =
    ( is-common-ratio-geometric-sequence-ℚ⁺ u n) ∙
    ( ap (mul-ℚ⁺ (seq-geometric-sequence-ℚ⁺ u n)) is-one-common-ratio) ∙
    ( right-unit-law-mul-ℚ⁺ (seq-geometric-sequence-ℚ⁺ u n)) ∙
    ( is-constant-seq-geometric-sequence-ℚ⁺ n)
```

### A geometric sequence of positive rational numbers with common ratio `r > 1` is strictly increasing

```agda
module _
  (u : geometric-sequence-ℚ⁺)
  (1<r : le-ℚ⁺ one-ℚ⁺ (common-ratio-geometric-sequence-ℚ⁺ u))
  where

  le-succ-seq-geometric-sequence-ℚ⁺ :
    (n : ℕ) →
    le-ℚ⁺
      ( seq-geometric-sequence-ℚ⁺ u n)
      ( seq-geometric-sequence-ℚ⁺ u (succ-ℕ n))
  le-succ-seq-geometric-sequence-ℚ⁺ n =
    binary-tr
      ( le-ℚ⁺)
      ( right-unit-law-mul-ℚ⁺ (seq-geometric-sequence-ℚ⁺ u n))
      ( inv (is-common-ratio-geometric-sequence-ℚ⁺ u n))
      ( preserves-le-left-mul-ℚ⁺
        ( seq-geometric-sequence-ℚ⁺ u n)
        ( one-ℚ)
        ( rational-ℚ⁺ (common-ratio-geometric-sequence-ℚ⁺ u))
        ( 1<r))

  is-strictly-increasing-seq-geometric-sequence-ℚ⁺ :
    is-strictly-increasing-sequence-Strictly-Preordered-Set
      ( strictly-preordered-set-ℚ⁺)
      ( seq-geometric-sequence-ℚ⁺ u)
  is-strictly-increasing-seq-geometric-sequence-ℚ⁺ =
    is-strictly-increasing-le-succ-sequence-Strictly-Preordered-Set
      ( strictly-preordered-set-ℚ⁺)
      ( seq-geometric-sequence-ℚ⁺ u)
      ( le-succ-seq-geometric-sequence-ℚ⁺)
```

### The pointwise product of geometric sequences of positive rational numbers is geometric

Moreover, the common ratio of the product of geometric seqeuences is the product
of the common ratios of the sequences.

```agda
module _
  (u v : geometric-sequence-ℚ⁺)
  where

  mul-common-ratio-geometric-sequence-ℚ⁺ : ℚ⁺
  mul-common-ratio-geometric-sequence-ℚ⁺ =
    mul-ℚ⁺
      ( common-ratio-geometric-sequence-ℚ⁺ u)
      ( common-ratio-geometric-sequence-ℚ⁺ v)

  seq-mul-geometric-sequence-ℚ⁺ : sequence ℚ⁺
  seq-mul-geometric-sequence-ℚ⁺ n =
    mul-ℚ⁺
      ( seq-geometric-sequence-ℚ⁺ u n)
      ( seq-geometric-sequence-ℚ⁺ v n)

  is-common-ratio-mul-geometric-sequence-ℚ⁺ :
    is-common-ratio-sequence-ℚ⁺
      seq-mul-geometric-sequence-ℚ⁺
      mul-common-ratio-geometric-sequence-ℚ⁺
  is-common-ratio-mul-geometric-sequence-ℚ⁺ n =
    ( ap-binary
      ( mul-ℚ⁺)
      ( is-common-ratio-geometric-sequence-ℚ⁺ u n)
      ( is-common-ratio-geometric-sequence-ℚ⁺ v n)) ∙
    ( eq-ℚ⁺
      ( interchange-law-mul-mul-ℚ
        ( rational-ℚ⁺ (seq-geometric-sequence-ℚ⁺ u n))
        ( rational-ℚ⁺ (common-ratio-geometric-sequence-ℚ⁺ u))
        ( rational-ℚ⁺ (seq-geometric-sequence-ℚ⁺ v n))
        ( rational-ℚ⁺ (common-ratio-geometric-sequence-ℚ⁺ v))))

  is-geometric-seq-mul-geometric-sequence-ℚ⁺ :
    is-geometric-sequence-ℚ⁺ seq-mul-geometric-sequence-ℚ⁺
  is-geometric-seq-mul-geometric-sequence-ℚ⁺ =
    mul-common-ratio-geometric-sequence-ℚ⁺ ,
    is-common-ratio-mul-geometric-sequence-ℚ⁺

  mul-geometric-sequence-ℚ⁺ : geometric-sequence-ℚ⁺
  mul-geometric-sequence-ℚ⁺ =
    seq-mul-geometric-sequence-ℚ⁺ ,
    is-geometric-seq-mul-geometric-sequence-ℚ⁺

  eq-common-ratio-mul-geometric-sequence-ℚ⁺ :
    ( mul-ℚ⁺
      ( common-ratio-geometric-sequence-ℚ⁺ u)
      ( common-ratio-geometric-sequence-ℚ⁺ v)) ＝
    ( common-ratio-geometric-sequence-ℚ⁺ mul-geometric-sequence-ℚ⁺)
  eq-common-ratio-mul-geometric-sequence-ℚ⁺ = refl
```

### The pointwise inverse of a geometric sequence of positive rational numbers is geometric

Moreover, the common ratio of the inverse of a geometric sequence is the inverse
of the common ratio of the sequence.

```agda
module _
  (u : geometric-sequence-ℚ⁺)
  where

  inv-common-ratio-geometric-sequence-ℚ⁺ : ℚ⁺
  inv-common-ratio-geometric-sequence-ℚ⁺ =
    inv-ℚ⁺ (common-ratio-geometric-sequence-ℚ⁺ u)

  seq-inv-geometric-sequence-ℚ⁺ : sequence ℚ⁺
  seq-inv-geometric-sequence-ℚ⁺ =
    map-sequence inv-ℚ⁺ (seq-geometric-sequence-ℚ⁺ u)

  is-common-ratio-inv-geometric-sequence-ℚ⁺ :
    is-common-ratio-sequence-ℚ⁺
      seq-inv-geometric-sequence-ℚ⁺
      inv-common-ratio-geometric-sequence-ℚ⁺
  is-common-ratio-inv-geometric-sequence-ℚ⁺ n =
    ( ap
      ( inv-ℚ⁺)
      ( is-common-ratio-geometric-sequence-ℚ⁺ u n)) ∙
    ( distributive-inv-mul-ℚ⁺
      ( seq-geometric-sequence-ℚ⁺ u n)
      ( common-ratio-geometric-sequence-ℚ⁺ u))

  is-geometric-seq-inv-geometric-sequence-ℚ⁺ :
    is-geometric-sequence-ℚ⁺ seq-inv-geometric-sequence-ℚ⁺
  is-geometric-seq-inv-geometric-sequence-ℚ⁺ =
    inv-common-ratio-geometric-sequence-ℚ⁺ ,
    is-common-ratio-inv-geometric-sequence-ℚ⁺

  inv-geometric-sequence-ℚ⁺ : geometric-sequence-ℚ⁺
  inv-geometric-sequence-ℚ⁺ =
    seq-inv-geometric-sequence-ℚ⁺ ,
    is-geometric-seq-inv-geometric-sequence-ℚ⁺

  eq-common-ratio-inv-geometric-sequence-ℚ⁺ :
    ( inv-ℚ⁺ (common-ratio-geometric-sequence-ℚ⁺ u)) ＝
    ( common-ratio-geometric-sequence-ℚ⁺ inv-geometric-sequence-ℚ⁺)
  eq-common-ratio-inv-geometric-sequence-ℚ⁺ = refl
```

## See also

- [Arithmetic sequences in ℚ⁺](elementary-number-theory.arithmetic-sequences-positive-rational-numbers.md):
  arithmetic sequences in the **additive** semigroup of ℚ⁺;
- [Bernoulli's inequality in ℚ⁺](elementary-number-theory.bernoullis-inequality-positive-rational-numbers.md):
  comparison between arithmetic and geometric sequences in ℚ⁺.

## External links

- [Geometric progressions](https://en.wikipedia.org/wiki/Geometric_progression)
  at Wikipedia
