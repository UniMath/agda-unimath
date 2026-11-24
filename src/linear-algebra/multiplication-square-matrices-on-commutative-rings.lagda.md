# Multiplication of square matrices on commutative rings

```agda
module linear-algebra.multiplication-square-matrices-on-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.monoids

open import linear-algebra.bilinear-maps-left-modules-commutative-rings
open import linear-algebra.identity-matrices-on-commutative-rings
open import linear-algebra.multiplication-matrices-on-commutative-rings
open import linear-algebra.multiplication-square-matrices-on-rings
open import linear-algebra.square-matrices-on-commutative-rings
```

</details>

## Idea

[Matrix multiplication](linear-algebra.multiplication-matrices-on-commutative-rings.md)
on [square matrices](linear-algebra.square-matrices-on-commutative-rings.md) on
a [commutative ring](commutative-algebra.commutative-rings.md) `R` is a
[bilinear map](linear-algebra.bilinear-maps-left-modules-commutative-rings.md).

## Definition

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (n : ℕ)
  where

  mul-square-matrix-Commutative-Ring :
    square-matrix-Commutative-Ring R n →
    square-matrix-Commutative-Ring R n →
    square-matrix-Commutative-Ring R n
  mul-square-matrix-Commutative-Ring =
    mul-square-matrix-Ring (ring-Commutative-Ring R) n
```

## Properties

### Associativity of matrix multiplication

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (n : ℕ)
  where

  abstract
    associative-mul-square-matrix-Commutative-Ring :
      (A B C : square-matrix-Commutative-Ring R n) →
      mul-square-matrix-Commutative-Ring R n
        ( mul-square-matrix-Commutative-Ring R n A B)
        ( C) ＝
      mul-square-matrix-Commutative-Ring R n
        ( A)
        ( mul-square-matrix-Commutative-Ring R n B C)
    associative-mul-square-matrix-Commutative-Ring =
      associative-mul-matrix-Commutative-Ring R n n n n
```

### Unit laws of square matrix multiplication

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (n : ℕ)
  where

  abstract
    left-unit-law-mul-square-matrix-Commutative-Ring :
      (A : square-matrix-Commutative-Ring R n) →
      mul-square-matrix-Commutative-Ring R n
        ( id-matrix-Commutative-Ring R n)
        ( A) ＝
      A
    left-unit-law-mul-square-matrix-Commutative-Ring =
      left-unit-law-mul-square-matrix-Ring (ring-Commutative-Ring R) n

    right-unit-law-mul-square-matrix-Commutative-Ring :
      (A : square-matrix-Commutative-Ring R n) →
      mul-square-matrix-Commutative-Ring R n
        ( A)
        ( id-matrix-Commutative-Ring R n) ＝
      A
    right-unit-law-mul-square-matrix-Commutative-Ring =
      right-unit-law-mul-square-matrix-Ring (ring-Commutative-Ring R) n
```

### Multiplication of square matrices in a commutative ring is a bilinear map

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (n : ℕ)
  where

  is-bilinear-map-mul-square-matrix-Commutative-Ring :
    is-bilinear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-square-matrix-Commutative-Ring R n)
      ( left-module-square-matrix-Commutative-Ring R n)
      ( left-module-square-matrix-Commutative-Ring R n)
      ( mul-square-matrix-Commutative-Ring R n)
  is-bilinear-map-mul-square-matrix-Commutative-Ring =
    is-bilinear-map-mul-matrix-Commutative-Ring R n n n

  bilinear-map-mul-square-matrix-Commutative-Ring :
    bilinear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-square-matrix-Commutative-Ring R n)
      ( left-module-square-matrix-Commutative-Ring R n)
      ( left-module-square-matrix-Commutative-Ring R n)
  bilinear-map-mul-square-matrix-Commutative-Ring =
    bilinear-map-mul-matrix-Commutative-Ring R n n n
```
