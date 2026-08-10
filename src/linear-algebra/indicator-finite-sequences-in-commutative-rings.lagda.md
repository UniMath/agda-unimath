# Indicator finite sequences in commutative rings

```agda
module linear-algebra.indicator-finite-sequences-in-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.universe-levels

open import linear-algebra.dot-product-finite-sequences-in-commutative-rings
open import linear-algebra.finite-sequences-in-commutative-rings
open import linear-algebra.indicator-finite-sequences-in-rings
open import linear-algebra.sums-of-finite-sequences-of-elements-left-modules-commutative-rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "indicator finite sequence" Disambiguation="in a commutative ring" Agda=indicator-fin-sequence-type-Commutative-Ring}}
in a [commutative ring](commutative-algebra.commutative-rings.md) `R` `χᵢ` for
index `i : Fin n` is a
[finite sequence](linear-algebra.finite-sequences-in-commutative-rings.md) in
`R` `u` such that `uᵢ = 1` and `uⱼ = 0` whenever `j ≠ i`.

## Definition

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (n : ℕ)
  (i : Fin n)
  where

  indicator-fin-sequence-type-Commutative-Ring :
    fin-sequence-type-Commutative-Ring R n
  indicator-fin-sequence-type-Commutative-Ring =
    indicator-fin-sequence-type-Ring (ring-Commutative-Ring R) n i

  abstract
    compute-at-index-indicator-fin-sequence-type-Commutative-Ring :
      indicator-fin-sequence-type-Commutative-Ring i ＝ one-Commutative-Ring R
    compute-at-index-indicator-fin-sequence-type-Commutative-Ring =
      compute-at-index-indicator-fin-sequence-type-Ring
        ( ring-Commutative-Ring R)
        ( n)
        ( i)

    compute-at-other-index-indicator-fin-sequence-type-Commutative-Ring :
      (j : Fin n) → i ≠ j →
      indicator-fin-sequence-type-Commutative-Ring j ＝ zero-Commutative-Ring R
    compute-at-other-index-indicator-fin-sequence-type-Commutative-Ring =
      compute-at-other-index-indicator-fin-sequence-type-Ring
        ( ring-Commutative-Ring R)
        ( n)
        ( i)
```

## Properties

### `χᵢⱼ = χⱼᵢ`

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (n : ℕ)
  where abstract

  symmetric-indicator-fin-sequence-type-Commutative-Ring :
    (i j : Fin n) →
    indicator-fin-sequence-type-Commutative-Ring R n i j ＝
    indicator-fin-sequence-type-Commutative-Ring R n j i
  symmetric-indicator-fin-sequence-type-Commutative-Ring =
    symmetric-indicator-fin-sequence-type-Ring (ring-Commutative-Ring R) n
```

### The dot product of an indicator sequence for index `i` with a finite sequence `v` is `v i`

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (n : ℕ)
  (i : Fin n)
  where abstract

  left-dot-product-indicator-fin-sequence-type-Commutative-Ring :
    (u : fin-sequence-type-Commutative-Ring R n) →
    dot-product-fin-sequence-type-Commutative-Ring R n
      ( indicator-fin-sequence-type-Commutative-Ring R n i)
      ( u) ＝
    u i
  left-dot-product-indicator-fin-sequence-type-Commutative-Ring =
    left-dot-product-indicator-fin-sequence-type-Ring
      ( ring-Commutative-Ring R)
      ( n)
      ( i)

  right-dot-product-indicator-fin-sequence-type-Commutative-Ring :
    (u : fin-sequence-type-Commutative-Ring R n) →
    dot-product-fin-sequence-type-Commutative-Ring R n
      ( u)
      ( indicator-fin-sequence-type-Commutative-Ring R n i) ＝
    u i
  right-dot-product-indicator-fin-sequence-type-Commutative-Ring =
    right-dot-product-indicator-fin-sequence-type-Ring
      ( ring-Commutative-Ring R)
      ( n)
      ( i)
```

### Every finite sequence in a commutative ring is a linear combination of indicator sequences

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (n : ℕ)
  (v : fin-sequence-type-Commutative-Ring R n)
  where abstract

  htpy-linear-combination-indicator-fin-sequence-type-Commutative-Ring :
    sum-fin-sequence-type-left-module-Commutative-Ring
      ( R)
      ( left-module-fin-sequence-Commutative-Ring R n)
      ( n)
      ( λ i →
        scalar-mul-fin-sequence-type-Commutative-Ring R n
          ( v i)
          ( indicator-fin-sequence-type-Commutative-Ring R n i)) ~
    v
  htpy-linear-combination-indicator-fin-sequence-type-Commutative-Ring =
    htpy-linear-combination-indicator-fin-sequence-type-Ring
      ( ring-Commutative-Ring R)
      ( n)
      ( v)

  eq-linear-combination-indicator-fin-sequence-type-Commutative-Ring :
    sum-fin-sequence-type-left-module-Commutative-Ring
      ( R)
      ( left-module-fin-sequence-Commutative-Ring R n)
      ( n)
      ( λ i →
        scalar-mul-fin-sequence-type-Commutative-Ring R n
          ( v i)
          ( indicator-fin-sequence-type-Commutative-Ring R n i)) ＝
    v
  eq-linear-combination-indicator-fin-sequence-type-Commutative-Ring =
    eq-htpy htpy-linear-combination-indicator-fin-sequence-type-Commutative-Ring
```
