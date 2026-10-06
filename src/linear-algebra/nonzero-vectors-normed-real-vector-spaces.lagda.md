# Nonzero vectors of normed real vector spaces

```agda
module linear-algebra.nonzero-vectors-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.apartness-normed-real-vector-spaces
open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.unit-vectors-normed-real-vector-spaces

open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

A
{{#concept "nonzero element" Disambiguation="of a normed real vector space" Agda=nonzero-vector-Normed-ℝ-Vector-Space}}
of a [normed real vector space](linear-algebra.normed-real-vector-spaces.md) is
a vector with [positive](real-numbers.positive-real-numbers.md) norm.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  is-nonzero-prop-Normed-ℝ-Vector-Space :
    subtype l1 (type-Normed-ℝ-Vector-Space V)
  is-nonzero-prop-Normed-ℝ-Vector-Space v =
    is-positive-prop-ℝ (map-norm-Normed-ℝ-Vector-Space V v)

  is-nonzero-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V → UU l1
  is-nonzero-Normed-ℝ-Vector-Space =
    is-in-subtype is-nonzero-prop-Normed-ℝ-Vector-Space

  nonzero-vector-Normed-ℝ-Vector-Space : UU (l1 ⊔ l2)
  nonzero-vector-Normed-ℝ-Vector-Space =
    type-subtype is-nonzero-prop-Normed-ℝ-Vector-Space
```

## Properties

### A vector is not nonzero if and only if it is zero

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (v : type-Normed-ℝ-Vector-Space V)
  where abstract

  is-zero-is-not-nonzero-Normed-ℝ-Vector-Space :
    ¬ is-nonzero-Normed-ℝ-Vector-Space V v →
    is-zero-Normed-ℝ-Vector-Space V v
  is-zero-is-not-nonzero-Normed-ℝ-Vector-Space ¬|v|>0 =
    is-extensional-norm-Normed-ℝ-Vector-Space V
      ( v)
      ( is-zero-is-nonnegative-is-nonpositive-ℝ
        ( is-nonpositive-is-not-positive-ℝ ¬|v|>0)
        ( is-nonnegative-map-norm-Normed-ℝ-Vector-Space V v))

  is-not-nonzero-is-zero-Normed-ℝ-Vector-Space :
    is-zero-Normed-ℝ-Vector-Space V v →
    ¬ is-nonzero-Normed-ℝ-Vector-Space V v
  is-not-nonzero-is-zero-Normed-ℝ-Vector-Space refl =
    is-not-positive-is-zero-ℝ
      ( _)
      ( is-zero-map-norm-zero-Normed-ℝ-Vector-Space V)
```

### Normalization of a nonzero vector to a unit vector

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ((v , |v|>0) : nonzero-vector-Normed-ℝ-Vector-Space V)
  (let |v|⁺ = (map-norm-Normed-ℝ-Vector-Space V v , |v|>0))
  where

  type-unit-nonzero-vector-Normed-ℝ-Vector-Space : type-Normed-ℝ-Vector-Space V
  type-unit-nonzero-vector-Normed-ℝ-Vector-Space =
    mul-Normed-ℝ-Vector-Space V (real-inv-ℝ⁺ |v|⁺) v

  abstract
    is-unit-type-unit-nonzero-vector-Normed-ℝ-Vector-Space :
      is-unit-Normed-ℝ-Vector-Space V
        ( type-unit-nonzero-vector-Normed-ℝ-Vector-Space)
    is-unit-type-unit-nonzero-vector-Normed-ℝ-Vector-Space =
      inv-tr
        ( λ n → sim-ℝ n one-ℝ)
        ( map-norm-mul-positive-Normed-ℝ-Vector-Space V (inv-ℝ⁺ |v|⁺) v)
        ( left-inverse-law-mul-ℝ⁺ |v|⁺)

  unit-nonzero-vector-Normed-ℝ-Vector-Space : unit-Normed-ℝ-Vector-Space V
  unit-nonzero-vector-Normed-ℝ-Vector-Space =
    ( type-unit-nonzero-vector-Normed-ℝ-Vector-Space ,
      is-unit-type-unit-nonzero-vector-Normed-ℝ-Vector-Space)
```

### Normalization of a nonzero vector to a target nonnegative norm

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (c : ℝ⁰⁺ l1)
  (v : nonzero-vector-Normed-ℝ-Vector-Space V)
  (let (v̂ , |v̂|=1) = unit-nonzero-vector-Normed-ℝ-Vector-Space V v)
  where

  normalized-to-norm-nonzero-vector-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V
  normalized-to-norm-nonzero-vector-Normed-ℝ-Vector-Space =
    mul-Normed-ℝ-Vector-Space V (real-ℝ⁰⁺ c) v̂

  abstract
    has-norm-normalized-to-norm-nonzero-vector-Normed-ℝ-Vector-Space :
      has-norm-Normed-ℝ-Vector-Space V
        ( c)
        ( normalized-to-norm-nonzero-vector-Normed-ℝ-Vector-Space)
    has-norm-normalized-to-norm-nonzero-vector-Normed-ℝ-Vector-Space =
      map-norm-mul-nonnegative-unit-Normed-ℝ-Vector-Space V c (v̂ , |v̂|=1)
```

### A vector is nonzero if and only if it is apart from zero

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (v : type-Normed-ℝ-Vector-Space V)
  where abstract

  is-apart-zero-is-nonzero-Normed-ℝ-Vector-Space :
    is-nonzero-Normed-ℝ-Vector-Space V v →
    apart-Normed-ℝ-Vector-Space V v (zero-Normed-ℝ-Vector-Space V)
  is-apart-zero-is-nonzero-Normed-ℝ-Vector-Space =
    inv-tr
      ( is-positive-ℝ)
      ( right-zero-law-dist-Normed-ℝ-Vector-Space V v)

  is-nonzero-is-apart-zero-Normed-ℝ-Vector-Space :
    apart-Normed-ℝ-Vector-Space V v (zero-Normed-ℝ-Vector-Space V) →
    is-nonzero-Normed-ℝ-Vector-Space V v
  is-nonzero-is-apart-zero-Normed-ℝ-Vector-Space =
    tr
      ( is-positive-ℝ)
      ( right-zero-law-dist-Normed-ℝ-Vector-Space V v)
```
