# Additive orders of elements of rings

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module ring-theory.additive-orders-of-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.integers

open import foundation.action-on-identifications-functions
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.normal-subgroups
open import group-theory.orders-of-elements-groups

open import ring-theory.integer-multiples-of-elements-rings
open import ring-theory.rings
```

</details>

## Idea

The **additive order** of an element `x` of a [ring](ring-theory.rings.md) `R`
is the [normal subgroup](group-theory.normal-subgroups.md) of the
[group `ℤ` of integers](elementary-number-theory.group-of-integers.md)
consisting of all [integers](elementary-number-theory.integers.md) `k` such that
`kx ＝ 0`.

## Definitions

### Additive orders of elements of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  additive-order-element-Ring : type-Ring R → Normal-Subgroup l ℤ-Group
  additive-order-element-Ring = order-element-Group (group-Ring R)
```

## Properties

### The order of any element divides the order of `1`

Suppose that `k·1 ＝ 0` for some integer `k`. Then we have

```text
  k·x ＝ k·(1x) ＝ (k·1)x ＝ 0x ＝ 0.
```

This shows that if the integer `k` is in the order of `1`, then it is in the
order of `x`. Therefore we conclude that the order of `x` always divides the
order of `1`.

```agda
module _
  {l : Level} (R : Ring l)
  where

  div-additive-order-element-additive-order-one-Ring :
    (x : type-Ring R) →
    div-order-element-Group (group-Ring R) x (one-Ring R)
  div-additive-order-element-additive-order-one-Ring x k H =
    ( ap (integer-multiple-Ring R k) (inv (left-unit-law-mul-Ring R x))) ∙
    ( inv (left-integer-multiple-law-mul-Ring R k _ _)) ∙
    ( ap (mul-Ring' R x) H) ∙
    ( left-zero-law-mul-Ring R x)
```

### If there exists an integer `k` such that `k·x ＝ y` then the order of `y` divides the order of `x`

```agda
module _
  {l : Level} (R : Ring l)
  where
```

### If there exists an integer `k` such that `k·x ＝ 1` then the order of `x` is the order of `1`

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-same-elements-additive-order-element-additive-order-one-Ring :
    (x : type-Ring R) →
    ∃ ℤ (λ k → integer-multiple-Ring R k x ＝ one-Ring R) →
    has-same-elements-Normal-Subgroup
      ( ℤ-Group)
      ( additive-order-element-Ring R x)
      ( additive-order-element-Ring R (one-Ring R))
  has-same-elements-additive-order-element-additive-order-one-Ring x H = {!!}
```
