# Multiplication of matrices on commutative rings

```agda
module linear-algebra.multiplication-matrices-on-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.bilinear-maps-left-modules-commutative-rings
open import linear-algebra.matrices-on-commutative-rings
open import linear-algebra.multiplication-matrices-on-rings
```

</details>

## Idea

[Matrix multiplication](linear-algebra.multiplication-matrices-on-rings.md) on
[commutative rings](commutative-algebra.commutative-rings.md) is a
[bilinear map](linear-algebra.bilinear-maps-left-modules-commutative-rings.md).

## Definition

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (m n p : ℕ)
  where

  mul-matrix-Commutative-Ring :
    matrix-Commutative-Ring R m n → matrix-Commutative-Ring R n p →
    matrix-Commutative-Ring R m p
  mul-matrix-Commutative-Ring =
    mul-matrix-Ring (ring-Commutative-Ring R) m n p
```

## Properties

### Multiplication of matrices is associative

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  where

  abstract
    associative-mul-matrix-Commutative-Ring :
      (m n p q : ℕ)
      (A : matrix-Commutative-Ring R m n)
      (B : matrix-Commutative-Ring R n p)
      (C : matrix-Commutative-Ring R p q) →
      mul-matrix-Commutative-Ring R m p q
        ( mul-matrix-Commutative-Ring R m n p A B)
        ( C) ＝
      mul-matrix-Commutative-Ring R m n q
        ( A)
        ( mul-matrix-Commutative-Ring R n p q B C)
    associative-mul-matrix-Commutative-Ring =
      associative-mul-matrix-Ring (ring-Commutative-Ring R)
```

### Multiplication of matrices is distributive over addition

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (m n p : ℕ)
  where

  abstract
    left-distributive-mul-add-matrix-Commutative-Ring :
      (A : matrix-Commutative-Ring R m n)
      (B C : matrix-Commutative-Ring R n p) →
      mul-matrix-Commutative-Ring R m n p
        ( A)
        ( add-matrix-Commutative-Ring R n p B C) ＝
      add-matrix-Commutative-Ring R m p
        ( mul-matrix-Commutative-Ring R m n p A B)
        ( mul-matrix-Commutative-Ring R m n p A C)
    left-distributive-mul-add-matrix-Commutative-Ring =
      left-distributive-mul-add-matrix-Ring (ring-Commutative-Ring R) m n p

    right-distributive-mul-add-matrix-Commutative-Ring :
      (A B : matrix-Commutative-Ring R m n)
      (C : matrix-Commutative-Ring R n p) →
      mul-matrix-Commutative-Ring R m n p
        ( add-matrix-Commutative-Ring R m n A B)
        ( C) ＝
      add-matrix-Commutative-Ring R m p
        ( mul-matrix-Commutative-Ring R m n p A C)
        ( mul-matrix-Commutative-Ring R m n p B C)
    right-distributive-mul-add-matrix-Commutative-Ring =
      right-distributive-mul-add-matrix-Ring (ring-Commutative-Ring R) m n p
```

### `(rA)B = r(AB)`

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (m n p : ℕ)
  where

  abstract
    associative-scalar-mul-mul-matrix-Commutative-Ring :
      (r : type-Commutative-Ring R)
      (A : matrix-Commutative-Ring R m n)
      (B : matrix-Commutative-Ring R n p) →
      mul-matrix-Commutative-Ring R m n p
        ( scalar-mul-matrix-Commutative-Ring R m n r A)
        ( B) ＝
      scalar-mul-matrix-Commutative-Ring R m p
        ( r)
        ( mul-matrix-Commutative-Ring R m n p A B)
    associative-scalar-mul-mul-matrix-Commutative-Ring =
      associative-scalar-mul-mul-matrix-Ring (ring-Commutative-Ring R) m n p
```

### `A(rB) = r(AB)`

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (m n p : ℕ)
  (A : matrix-Commutative-Ring R m n)
  (r : type-Commutative-Ring R)
  (B : matrix-Commutative-Ring R n p)
  where

  abstract
    htpy-left-swap-mul-scalar-mul-matrix-Ring :
      binary-htpy
        ( mul-matrix-Commutative-Ring R m n p
          ( A)
          ( scalar-mul-matrix-Commutative-Ring R n p r B))
        ( scalar-mul-matrix-Commutative-Ring R m p
          ( r)
          ( mul-matrix-Commutative-Ring R m n p A B))
    htpy-left-swap-mul-scalar-mul-matrix-Ring i k =
      ( htpy-sum-fin-sequence-type-Commutative-Ring R n
        ( λ j → left-swap-mul-Commutative-Ring R (A i j) r (B j k))) ∙
      ( inv
        ( left-distributive-mul-sum-fin-sequence-type-Commutative-Ring R n r _))

    left-swap-mul-scalar-mul-matrix-Ring :
      mul-matrix-Commutative-Ring R m n p
        ( A)
        ( scalar-mul-matrix-Commutative-Ring R n p r B) ＝
      scalar-mul-matrix-Commutative-Ring R m p
        ( r)
        ( mul-matrix-Commutative-Ring R m n p A B)
    left-swap-mul-scalar-mul-matrix-Ring =
      eq-binary-htpy _ _ htpy-left-swap-mul-scalar-mul-matrix-Ring
```

### Matrix multiplication is a bilinear map

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (m n p : ℕ)
  where

  is-linear-on-left-mul-matrix-Commutative-Ring :
    is-linear-on-left-binary-map-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring R m n)
      ( left-module-matrix-Commutative-Ring R n p)
      ( left-module-matrix-Commutative-Ring R m p)
      ( mul-matrix-Commutative-Ring R m n p)
  is-linear-on-left-mul-matrix-Commutative-Ring B =
    ( ( λ A A' →
        right-distributive-mul-add-matrix-Commutative-Ring R m n p A A' B) ,
      ( λ r A →
        associative-scalar-mul-mul-matrix-Commutative-Ring R m n p r A B))

  is-linear-on-right-mul-matrix-Commutative-Ring :
    is-linear-on-right-binary-map-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring R m n)
      ( left-module-matrix-Commutative-Ring R n p)
      ( left-module-matrix-Commutative-Ring R m p)
      ( mul-matrix-Commutative-Ring R m n p)
  is-linear-on-right-mul-matrix-Commutative-Ring A =
    ( left-distributive-mul-add-matrix-Commutative-Ring R m n p A ,
      left-swap-mul-scalar-mul-matrix-Ring R m n p A)

  is-bilinear-map-mul-matrix-Commutative-Ring :
    is-bilinear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring R m n)
      ( left-module-matrix-Commutative-Ring R n p)
      ( left-module-matrix-Commutative-Ring R m p)
      ( mul-matrix-Commutative-Ring R m n p)
  is-bilinear-map-mul-matrix-Commutative-Ring =
    ( is-linear-on-left-mul-matrix-Commutative-Ring ,
      is-linear-on-right-mul-matrix-Commutative-Ring)

  bilinear-map-mul-matrix-Commutative-Ring :
    bilinear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring R m n)
      ( left-module-matrix-Commutative-Ring R n p)
      ( left-module-matrix-Commutative-Ring R m p)
  bilinear-map-mul-matrix-Commutative-Ring =
    ( mul-matrix-Commutative-Ring R m n p ,
      is-bilinear-map-mul-matrix-Commutative-Ring)
```
