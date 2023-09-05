# Commuting elements of groups

```agda
module group-theory.commuting-elements-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.groups
```

</details>

## Idea

Two elements `x` and `y` of a [group](group-theory.groups.md) `G` are said to
**commute** if the equality `xy ＝ yx` holds. For any element `x`, the subset of
elements that commute with `x` form a subgroup of `G` called the
[centralizer](group-theory.centralizer-subgroups.md) of the element `x`.

## Definitions

### Commuting elements

```agda
module _
  {l : Level} (G : Group l)
  where

  commute-prop-Group : (x y : type-Group G) → Prop l
  commute-prop-Group x y =
    Id-Prop (set-Group G) (mul-Group G x y) (mul-Group G y x)

  commute-Group : (x y : type-Group G) → UU l
  commute-Group x y = type-Prop (commute-prop-Group x y)

  is-prop-commute-Group : (x y : type-Group G) → is-prop (commute-Group x y)
  is-prop-commute-Group x y = is-prop-type-Prop (commute-prop-Group x y)
```

## Properties

### The relation `commute-Group` is reflexive

```agda
module _
  {l : Level} (G : Group l)
  where

  refl-commute-Group : (x : type-Group G) → commute-Group G x x
  refl-commute-Group x = refl
```

### The relation `commute-Group` is symmetric

```agda
module _
  {l : Level} (G : Group l)
  where

  symmetric-commute-Group :
    (x y : type-Group G) → commute-Group G x y → commute-Group G y x
  symmetric-commute-Group x y = inv
```

### The unit element commutes with every element of the group

```agda
module _
  {l : Level} (G : Group l)
  where

  commute-unit-Group : (x : type-Group G) → commute-Group G x (unit-Group G)
  commute-unit-Group x =
    right-unit-law-mul-Group G x ∙ inv (left-unit-law-mul-Group G x)
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

    infix 50 _*_
    _*_ = mul-Group G

  left-swap-commute-Group :
    (x y z : type-Group G) → commute-Group G x y →
    x * (y * z) ＝ y * (x * z)
  left-swap-commute-Group x y z H =
    ( inv (associative-mul-Group G _ _ _)) ∙
    ( ( ap (_* z) H) ∙
      ( associative-mul-Group G _ _ _))

  right-swap-commute-Group :
    (x y z : type-Group G) → commute-Group G y z →
    (x * y) * z ＝ (x * z) * y
  right-swap-commute-Group x y z H =
    ( associative-mul-Group G _ _ _) ∙
    ( ( ap (x *_) H) ∙
      ( inv (associative-mul-Group G _ _ _)))
```

### If `x` commutes with `y` and with `z`, then `x` commutes with `yz`

```agda
module _
  {l : Level} (G : Group l)
  where

  private

    infix 50 _*_
    _*_ = mul-Group G

  commute-mul-Group :
    (x y z : type-Group G) →
    commute-Group G x y → commute-Group G x z →
    commute-Group G x (mul-Group G y z)
  commute-mul-Group x y z H K =
    equational-reasoning
      (x * (y * z))
      ＝ y * (x * z) by left-swap-commute-Group G _ _ _ H
      ＝ y * (z * x) by ap (y *_) K
      ＝ (y * z) * x by inv (associative-mul-Group G _ _ _)
```

### An interchange law for commuting elements in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  private

    infix 50 _*_
    _*_ = mul-Group G

  interchange-mul-mul-Group :
    {x y z w : type-Group G} →
    commute-Group G y z → (x * y) * (z * w) ＝ (x * z) * (y * w)
  interchange-mul-mul-Group {x} {y} {z} {w} H =
    equational-reasoning
      (x * y) * (z * w)
      ＝ x * (y * (z * w)) by associative-mul-Group G _ _ _
      ＝ x * (z * (y * w)) by ap (x *_) (left-swap-commute-Group G _ _ _ H)
      ＝ (x * z) * (y * w) by inv (associative-mul-Group G _ _ _)
```
