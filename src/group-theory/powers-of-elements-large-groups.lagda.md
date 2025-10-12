# Powers of elements in large groups

```agda
module group-theory.powers-of-elements-large-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.large-groups
open import group-theory.powers-of-elements-groups
open import group-theory.powers-of-elements-large-monoids
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising an element of a large group to a natural number power" Agda=power-Large-Group}}
on a [large group](group-theory.large-groups.md) is the map `n x ↦ xⁿ`, which is
defined by [iteratively](foundation.iterating-functions.md) multiplying `x` with
itself `n` times. In this file we consider the case where `n` is a
[natural number](elementary-number-theory.natural-numbers.md).

## Definitions

### Powers of elements of groups

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  power-Large-Group :
    {l : Level} (n : ℕ) → type-Large-Group G l → type-Large-Group G l
  power-Large-Group {l} = power-Group (group-Large-Group G l)
```

## Properties

### The power operation preserves similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    preserves-sim-power-Large-Group :
      {l1 l2 : Level} (n : ℕ) →
      (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      sim-Large-Group G x y →
      sim-Large-Group G (power-Large-Group G n x) (power-Large-Group G n y)
    preserves-sim-power-Large-Group =
      preserves-sim-power-Large-Monoid (large-monoid-Large-Group G)
```

### `1ⁿ = 1`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    raise-power-unit-Large-Group :
      (l : Level) (n : ℕ) →
      power-Large-Group G n (raise-unit-Large-Group G l) ＝
      raise-unit-Large-Group G l
    raise-power-unit-Large-Group =
      raise-power-unit-Large-Monoid (large-monoid-Large-Group G)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    power-succ-Large-Group :
      {l : Level} (n : ℕ) (x : type-Large-Group G l) →
      power-Large-Group G (succ-ℕ n) x ＝
      mul-Large-Group G (power-Large-Group G n x) x
    power-succ-Large-Group =
      power-succ-Large-Monoid (large-monoid-Large-Group G)
```

### `xⁿ⁺¹ = xxⁿ`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    power-succ-Large-Group' :
      {l : Level} (n : ℕ) (x : type-Large-Group G l) →
      power-Large-Group G (succ-ℕ n) x ＝
      mul-Large-Group G x (power-Large-Group G n x)
    power-succ-Large-Group' =
      power-succ-Large-Monoid' (large-monoid-Large-Group G)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    distributive-power-add-Large-Group :
      {l : Level} (m n : ℕ) {x : type-Large-Group G l} →
      power-Large-Group G (m +ℕ n) x ＝
      mul-Large-Group G (power-Large-Group G m x) (power-Large-Group G n x)
    distributive-power-add-Large-Group =
      distributive-power-add-Large-Monoid (large-monoid-Large-Group G)
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    commute-powers-Large-Group :
      {l1 l2 : Level} (m n : ℕ) →
      {x : type-Large-Group G l1} {y : type-Large-Group G l2} →
      ( mul-Large-Group G x y ＝ mul-Large-Group G y x) →
      ( mul-Large-Group G
        ( power-Large-Group G m x)
        ( power-Large-Group G n y)) ＝
      ( mul-Large-Group G
        ( power-Large-Group G n y)
        ( power-Large-Group G m x))
    commute-powers-Large-Group =
      commute-powers-Large-Monoid (large-monoid-Large-Group G)
```

### If `x` commutes with `y`, their powers distribute over the product of `x` and `y`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  open similarity-reasoning-Large-Group G

  private
    _*_ = mul-Large-Group G

  abstract
    distributive-power-mul-Large-Group :
      {l1 l2 : Level} (n : ℕ) →
      {x : type-Large-Group G l1} {y : type-Large-Group G l2} →
      (mul-Large-Group G x y ＝ mul-Large-Group G y x) →
      power-Large-Group G n (mul-Large-Group G x y) ＝
      mul-Large-Group G (power-Large-Group G n x) (power-Large-Group G n y)
    distributive-power-mul-Large-Group =
      distributive-power-mul-Large-Monoid (large-monoid-Large-Group G)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    power-mul-Large-Group :
      {l : Level} (m n : ℕ) {x : type-Large-Group G l} →
      power-Large-Group G (m *ℕ n) x ＝
      power-Large-Group G n (power-Large-Group G m x)
    power-mul-Large-Group = power-mul-Large-Monoid (large-monoid-Large-Group G)
```

## See also

- [Integer powers of elements of large groups](group-theory.integer-powers-of-elements-large-groups.md)
