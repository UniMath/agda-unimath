# Powers of elements in groups

```agda
module group-theory.powers-of-elements-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.commuting-elements-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.powers-of-elements-monoids
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising an element of a group to a natural number power" Agda=power-Group}}
on a [group](group-theory.groups.md) is the map `n x ↦ xⁿ`, which is defined by
[iteratively](foundation.iterating-functions.md) multiplying `x` with itself `n`
times. This file describes the case where `n` is a
[natural number](elementary-number-theory.natural-numbers.md).

## Definition

### Powers by natural numbers of group elements

```agda
module _
  {l : Level} (G : Group l)
  where

  power-Group : ℕ → type-Group G → type-Group G
  power-Group = power-Monoid (monoid-Group G)
```

### The predicate of being a power of an element in a group

We say that an element `y` **is a power** of an element `x` if there
[exists](foundation.existential-quantification.md) a number `n` such that
`xⁿ ＝ y`.

```agda
module _
  {l : Level} (G : Group l)
  where

  is-power-of-element-prop-Group :
    (x y : type-Group G) → Prop l
  is-power-of-element-prop-Group =
    is-power-of-element-prop-Monoid (monoid-Group G)

  is-power-of-element-Group :
    (x y : type-Group G) → UU l
  is-power-of-element-Group =
    is-power-of-element-Monoid (monoid-Group G)

  is-prop-is-power-of-element-Group :
    (x y : type-Group G) →
    is-prop (is-power-of-element-Group x y)
  is-prop-is-power-of-element-Group =
    is-prop-is-power-of-element-Monoid (monoid-Group G)
```

## Properties

### `1ⁿ ＝ 1`

```agda
module _
  {l : Level} (G : Group l)
  where

  power-unit-Group :
    (n : ℕ) → power-Group G n (unit-Group G) ＝ unit-Group G
  power-unit-Group = power-unit-Monoid (monoid-Group G)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {l : Level} (G : Group l)
  where

  power-succ-Group :
    (n : ℕ) (x : type-Group G) →
    power-Group G (succ-ℕ n) x ＝ mul-Group G (power-Group G n x) x
  power-succ-Group = power-succ-Monoid (monoid-Group G)
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {l : Level} (G : Group l)
  where

  power-succ-Group' :
    (n : ℕ) (x : type-Group G) →
    power-Group G (succ-ℕ n) x ＝ mul-Group G x (power-Group G n x)
  power-succ-Group' = power-succ-Monoid' (monoid-Group G)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (G : Group l)
  where

  distributive-power-add-Group :
    (m n : ℕ) {x : type-Group G} →
    power-Group G (m +ℕ n) x ＝
    mul-Group G (power-Group G m x) (power-Group G n x)
  distributive-power-add-Group = distributive-power-add-Monoid (monoid-Group G)
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {l : Level} (G : Group l)
  where

  commute-powers-Group' :
    (n : ℕ) {x y : type-Group G} →
    commute-Group G x y → commute-Group G (power-Group G n x) y
  commute-powers-Group' = commute-powers-Monoid' (monoid-Group G)

  commute-powers-Group :
    (m n : ℕ) {x y : type-Group G} →
    commute-Group G x y →
    commute-Group G (power-Group G m x) (power-Group G n y)
  commute-powers-Group = commute-powers-Monoid (monoid-Group G)
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {l : Level} (G : Group l)
  where

  distributive-power-mul-Group :
    (n : ℕ) {x y : type-Group G} →
    (H : mul-Group G x y ＝ mul-Group G y x) →
    power-Group G n (mul-Group G x y) ＝
    mul-Group G (power-Group G n x) (power-Group G n y)
  distributive-power-mul-Group =
    distributive-power-mul-Monoid (monoid-Group G)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {l : Level} (G : Group l)
  where

  power-mul-Group :
    (m n : ℕ) {x : type-Group G} →
    power-Group G (m *ℕ n) x ＝ power-Group G n (power-Group G m x)
  power-mul-Group = power-mul-Monoid (monoid-Group G)
```

### Group homomorphisms preserve powers

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  preserves-powers-hom-Group :
    (n : ℕ) (x : type-Group G) →
    map-hom-Group G H f (power-Group G n x) ＝
    power-Group H n (map-hom-Group G H f x)
  preserves-powers-hom-Group =
    preserves-powers-hom-Monoid
      ( monoid-Group G)
      ( monoid-Group H)
      ( hom-monoid-hom-Group G H f)
```

## See also

- [Integer powers of elements in groups](group-theory.integer-powers-of-elements-groups.md)
