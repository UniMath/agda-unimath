# Commuting elements of groups

```agda
module group-theory.commuting-elements-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.commuting-elements-monoids
open import group-theory.groups
```

</details>

## Idea

Two elements `x` and `y` of a [group](group-theory.groups.md) `G` are said to
**commute** if the equality `xy ＝ yx` holds. For any element `x`, the subset of
elements that commute with `x` form a [subgroup](group-theory.subgroups.md) of
`G` called the [centralizer](group-theory.centralizer-subgroups.md) of the
element `x`.

## Definitions

### Commuting elements

```agda
module _
  {l : Level} (G : Group l)
  where

  commute-prop-Group : (x y : type-Group G) → Prop l
  commute-prop-Group = commute-prop-Monoid (monoid-Group G)

  commute-Group : (x y : type-Group G) → UU l
  commute-Group = commute-Monoid (monoid-Group G)

  commute-Group' : (x y : type-Group G) → UU l
  commute-Group' = commute-Monoid' (monoid-Group G)

  is-prop-commute-Group : (x y : type-Group G) → is-prop (commute-Group x y)
  is-prop-commute-Group = is-prop-commute-Monoid (monoid-Group G)
```

## Properties

### The relation `commute-Group` is reflexive

```agda
module _
  {l : Level} (G : Group l)
  where

  refl-commute-Group : (x : type-Group G) → commute-Group G x x
  refl-commute-Group = refl-commute-Monoid (monoid-Group G)
```

### The relation `commute-Group` is symmetric

```agda
module _
  {l : Level} (G : Group l)
  where

  symmetric-commute-Group :
    (x y : type-Group G) → commute-Group G x y → commute-Group G y x
  symmetric-commute-Group = symmetric-commute-Monoid (monoid-Group G)
```

### The unit element commutes with every element of the group

```agda
module _
  {l : Level} (G : Group l)
  where

  commute-unit-Group : (x : type-Group G) → commute-Group G x (unit-Group G)
  commute-unit-Group = commute-unit-Monoid (monoid-Group G)
```

### If `x` commutes with `y`, then `x` commutes with `y⁻¹`

```agda
module _
  {l : Level} (G : Group l)
  where

  commute-inv-Group :
    (x y : type-Group G) →
    commute-Group G x y → commute-Group G x (inv-Group G y)
  commute-inv-Group x y H =
    double-transpose-eq-mul-Group' G (inv H)
```

### If `x` commutes with `y`, then `x * (y * z) ＝ y * (x * z)` for any element `z`

```agda
module _
  {l : Level} (G : Group l)
  where

  private
    infix 45 _*_
    _*_ = mul-Group G

  left-swap-commute-Group :
    (x y z : type-Group G) → commute-Group G x y →
    x * (y * z) ＝ y * (x * z)
  left-swap-commute-Group = left-swap-commute-Monoid (monoid-Group G)

  right-swap-commute-Group :
    (x y z : type-Group G) → commute-Group G y z →
    (x * y) * z ＝ (x * z) * y
  right-swap-commute-Group = right-swap-commute-Monoid (monoid-Group G)
```

### If `x` commutes with `y` and with `z`, then `x` commutes with `yz`

```agda
module _
  {l : Level} (G : Group l)
  where

  commute-mul-Group :
    (x y z : type-Group G) →
    commute-Group G x y → commute-Group G x z →
    commute-Group G x (mul-Group G y z)
  commute-mul-Group = commute-mul-Monoid (monoid-Group G)
```
