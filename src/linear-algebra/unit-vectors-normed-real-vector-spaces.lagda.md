# Unit vectors in normed real vector spaces

```agda
module linear-algebra.unit-vectors-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.large-monoids

open import linear-algebra.normed-real-vector-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.large-multiplicative-monoid-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

A
{{#concept "unit vector" WDID=Q36255 WD="unit vector" Agda=unit-Normed-ℝ-Vector-Space}}
in a [normed real vector space](linear-algebra.normed-real-vector-spaces.md) `V`
is a vector `v : V` with norm [similar](real-numbers.similarity-real-numbers.md)
to [one](real-numbers.rational-real-numbers.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  is-unit-prop-Normed-ℝ-Vector-Space :
    subtype l1 (type-Normed-ℝ-Vector-Space V)
  is-unit-prop-Normed-ℝ-Vector-Space v =
    sim-prop-ℝ (map-norm-Normed-ℝ-Vector-Space V v) one-ℝ

  is-unit-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V → UU l1
  is-unit-Normed-ℝ-Vector-Space =
    is-in-subtype is-unit-prop-Normed-ℝ-Vector-Space

  unit-Normed-ℝ-Vector-Space : UU (l1 ⊔ l2)
  unit-Normed-ℝ-Vector-Space =
    type-subtype is-unit-prop-Normed-ℝ-Vector-Space

  type-unit-Normed-ℝ-Vector-Space :
    unit-Normed-ℝ-Vector-Space → type-Normed-ℝ-Vector-Space V
  type-unit-Normed-ℝ-Vector-Space =
    inclusion-subtype is-unit-prop-Normed-ℝ-Vector-Space
```

## Properties

### Multiplying a unit vector by a scalar `c` produces a vector with norm `|c|`

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where abstract

  map-norm-mul-unit-Normed-ℝ-Vector-Space :
    (c : ℝ l1) (v : unit-Normed-ℝ-Vector-Space V) →
    has-norm-Normed-ℝ-Vector-Space V
      ( nonnegative-abs-ℝ c)
      ( mul-Normed-ℝ-Vector-Space V c (type-unit-Normed-ℝ-Vector-Space V v))
  map-norm-mul-unit-Normed-ℝ-Vector-Space c (v , |v|~1) =
    equational-reasoning
      map-norm-Normed-ℝ-Vector-Space V (mul-Normed-ℝ-Vector-Space V c v)
      ＝ abs-ℝ c *ℝ map-norm-Normed-ℝ-Vector-Space V v
        by is-absolutely-homogeneous-norm-Normed-ℝ-Vector-Space V c v
      ＝ abs-ℝ c
        by
          eq-sim-ℝ
            ( sim-right-is-unit-law-mul-Large-Monoid
              ( large-monoid-mul-ℝ)
              ( abs-ℝ c)
              ( map-norm-Normed-ℝ-Vector-Space V v)
              ( |v|~1))

  map-norm-mul-nonnegative-unit-Normed-ℝ-Vector-Space :
    (c : ℝ⁰⁺ l1) (v : unit-Normed-ℝ-Vector-Space V) →
    has-norm-Normed-ℝ-Vector-Space V
      ( c)
      ( mul-Normed-ℝ-Vector-Space V
        ( real-ℝ⁰⁺ c)
        ( type-unit-Normed-ℝ-Vector-Space V v))
  map-norm-mul-nonnegative-unit-Normed-ℝ-Vector-Space c v =
    ( map-norm-mul-unit-Normed-ℝ-Vector-Space (real-ℝ⁰⁺ c) v) ∙
    ( abs-real-ℝ⁰⁺ c)

  map-norm-mul-positive-unit-Normed-ℝ-Vector-Space :
    (c : ℝ⁺ l1) (v : unit-Normed-ℝ-Vector-Space V) →
    has-norm-Normed-ℝ-Vector-Space V
      ( nonnegative-ℝ⁺ c)
      ( mul-Normed-ℝ-Vector-Space V
        ( real-ℝ⁺ c)
        ( type-unit-Normed-ℝ-Vector-Space V v))
  map-norm-mul-positive-unit-Normed-ℝ-Vector-Space c =
    map-norm-mul-nonnegative-unit-Normed-ℝ-Vector-Space (nonnegative-ℝ⁺ c)
```

## External links

- [Unit vector](https://en.wikipedia.org/wiki/Unit_vector) on Wikipedia
