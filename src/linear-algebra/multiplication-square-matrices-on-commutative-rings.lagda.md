# Multiplication of square matrices on commutative rings

```agda
module linear-algebra.multiplication-square-matrices-on-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-commutative-rings
open import commutative-algebra.associative-algebras-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.unital-associative-algebras-commutative-rings

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

`n × n`
[square matrices](linear-algebra.square-matrices-on-commutative-rings.md) on a
[commutative ring](commutative-algebra.commutative-rings.md) `R` form a
[unital associative algebra](commutative-algebra.unital-associative-algebras-commutative-rings.md)
on `R` under
[matrix multiplication](linear-algebra.multiplication-matrices-on-commutative-rings.md).

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

### Square matrices on a commutative ring form a unital associative algebra

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (n : ℕ)
  where

  algebra-square-matrix-Commutative-Ring : algebra-Commutative-Ring l R
  algebra-square-matrix-Commutative-Ring =
    ( left-module-square-matrix-Commutative-Ring R n ,
      bilinear-map-mul-square-matrix-Commutative-Ring R n)

  associative-algebra-square-matrix-Commutative-Ring :
    associative-algebra-Commutative-Ring l R
  associative-algebra-square-matrix-Commutative-Ring =
    ( algebra-square-matrix-Commutative-Ring ,
      associative-mul-square-matrix-Commutative-Ring R n)

  unital-associative-algebra-square-matrix-Commutative-Ring :
    unital-associative-algebra-Commutative-Ring l R
  unital-associative-algebra-square-matrix-Commutative-Ring =
    ( associative-algebra-square-matrix-Commutative-Ring ,
      id-matrix-Commutative-Ring R n ,
      left-unit-law-mul-square-matrix-Commutative-Ring R n ,
      right-unit-law-mul-square-matrix-Commutative-Ring R n)

  monoid-mul-square-matrix-Commutative-Ring : Monoid l
  monoid-mul-square-matrix-Commutative-Ring =
    monoid-mul-unital-associative-algebra-Commutative-Ring
      ( R)
      ( unital-associative-algebra-square-matrix-Commutative-Ring)
```
