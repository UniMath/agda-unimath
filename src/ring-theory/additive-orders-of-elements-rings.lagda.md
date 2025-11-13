# Additive orders of elements of rings

```agda
module ring-theory.additive-orders-of-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.integers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import group-theory.normal-subgroups
open import group-theory.orders-of-elements-groups
open import group-theory.subgroups
open import group-theory.subsets-groups

open import ring-theory.integer-multiples-of-elements-rings
open import ring-theory.rings
```

</details>

## Idea

The
{{#concept "additive order" Disambiguation="of an element of a ring" Agda=additive-order-element-Ring}}
of an element `x` of a [ring](ring-theory.rings.md) `R` is the
[normal subgroup](group-theory.normal-subgroups.md) of the
[group `ℤ` of integers](elementary-number-theory.group-of-integers.md)
consisting of all [integers](elementary-number-theory.integers.md) `k` such that
`kx ＝ 0`.

## Definitions

### Additive orders of elements of rings

```agda
module _
  {l : Level} (R : Ring l) (x : type-Ring R)
  where

  additive-order-element-Ring : Normal-Subgroup l ℤ-Group
  additive-order-element-Ring = order-element-Group (group-Ring R) x

  subgroup-additive-order-element-Ring : Subgroup l ℤ-Group
  subgroup-additive-order-element-Ring =
    subgroup-order-element-Group (group-Ring R) x

  subset-additive-order-element-Ring : subset-Group l ℤ-Group
  subset-additive-order-element-Ring =
    subset-order-element-Group (group-Ring R) x

  is-in-additive-order-element-Ring : ℤ → UU l
  is-in-additive-order-element-Ring =
    is-in-order-element-Group (group-Ring R) x
```

### Divisibility of additive orders of elements of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  div-additive-order-element-Ring :
    (x y : type-Ring R) → UU l
  div-additive-order-element-Ring =
    div-order-element-Group (group-Ring R)
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
    ( inv (left-zero-law-mul-Ring R x)) ∙
    ( ap (mul-Ring' R x) H) ∙
    ( left-integer-multiple-law-mul-Ring R k _ _) ∙
    ( ap (integer-multiple-Ring R k) (left-unit-law-mul-Ring R x))
```

### If there exists an integer `k` such that `k·x ＝ y` then the order of `y` divides the order of `x`

**Proof:** Suppose that `k·x ＝ y` and `l·x ＝ 0`, then it follows that

```text
  l·y ＝ l·(k·x) ＝ k·(l·x) ＝ k·0 ＝ 0.
```

```agda
module _
  {l : Level} (R : Ring l)
  where

  div-additive-order-element-is-integer-multiple-Ring :
    (x y : type-Ring R) → is-integer-multiple-of-element-Ring R x y →
    div-additive-order-element-Ring R y x
  div-additive-order-element-is-integer-multiple-Ring x y H l p =
    apply-universal-property-trunc-Prop H
      ( subset-additive-order-element-Ring R y l)
      ( λ (k , q) →
        ( inv (left-zero-law-integer-multiple-Ring R k)) ∙
        ( ap (integer-multiple-Ring R k) p) ∙
        ( swap-integer-multiple-Ring R k l x ∙
        ( ap (integer-multiple-Ring R l) q)))
```

### If there exists an integer `k` such that `k·x ＝ 1` then the order of `x` is the order of `1`

In other words, if there exists an integer `k` such that `k·x ＝ 1`, then the
additive order of `x` is the
[characteristic](ring-theory.characteristics-rings.md) of the ring `R`.

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-same-elements-additive-order-element-additive-order-one-Ring :
    (x : type-Ring R) →
    is-integer-multiple-of-element-Ring R x (one-Ring R) →
    has-same-elements-Normal-Subgroup
      ( ℤ-Group)
      ( additive-order-element-Ring R x)
      ( additive-order-element-Ring R (one-Ring R))
  pr1 (has-same-elements-additive-order-element-additive-order-one-Ring x H y) =
    div-additive-order-element-is-integer-multiple-Ring R x (one-Ring R) H y
  pr2 (has-same-elements-additive-order-element-additive-order-one-Ring x H y) =
    div-additive-order-element-additive-order-one-Ring R x y

  eq-additive-order-element-additive-order-one-Ring :
    (x : type-Ring R) → is-integer-multiple-of-element-Ring R x (one-Ring R) →
    additive-order-element-Ring R x ＝
    additive-order-element-Ring R (one-Ring R)
  eq-additive-order-element-additive-order-one-Ring x H =
    eq-has-same-elements-Normal-Subgroup
      ( ℤ-Group)
      ( additive-order-element-Ring R x)
      ( additive-order-element-Ring R (one-Ring R))
      ( has-same-elements-additive-order-element-additive-order-one-Ring x H)
```
