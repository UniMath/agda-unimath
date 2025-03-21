# Commuting elements of semigroups

```agda
module group-theory.commuting-elements-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

Two elements `x` and `y` of a [semigroup](group-theory.semigroups.md) are said
to **commute** if `xy ＝ yx`.

## Definitions

### Commuting elements

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  commute-prop-Semigroup : (x y : type-Semigroup G) → Prop l
  commute-prop-Semigroup x y =
    Id-Prop (set-Semigroup G) (mul-Semigroup G x y) (mul-Semigroup G y x)

  commute-Semigroup : (x y : type-Semigroup G) → UU l
  commute-Semigroup x y = type-Prop (commute-prop-Semigroup x y)

  commute-Semigroup' : (x y : type-Semigroup G) → UU l
  commute-Semigroup' x y = commute-Semigroup y x

  is-prop-commute-Semigroup :
    (x y : type-Semigroup G) → is-prop (commute-Semigroup x y)
  is-prop-commute-Semigroup x y = is-prop-type-Prop (commute-prop-Semigroup x y)
```

## Properties

### The relation `commute-Semigroup` is reflexive

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  refl-commute-Semigroup : (x : type-Semigroup G) → commute-Semigroup G x x
  refl-commute-Semigroup x = refl
```

### The relation `commute-Semigroup` is symmetric

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  symmetric-commute-Semigroup :
    (x y : type-Semigroup G) → commute-Semigroup G x y → commute-Semigroup G y x
  symmetric-commute-Semigroup x y = inv
```

### If `x` commutes with `y`, then `x * (y * z) ＝ y * (x * z)` for any element `z`

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  private
    infix 45 _*_
    _*_ = mul-Semigroup G

  left-swap-commute-Semigroup :
    (x y z : type-Semigroup G) → commute-Semigroup G x y →
    x * (y * z) ＝ y * (x * z)
  left-swap-commute-Semigroup x y z H =
    ( inv (associative-mul-Semigroup G _ _ _)) ∙
    ( ap (_* z) H) ∙
    ( associative-mul-Semigroup G _ _ _)

  right-swap-commute-Semigroup :
    (x y z : type-Semigroup G) → commute-Semigroup G y z →
    (x * y) * z ＝ (x * z) * y
  right-swap-commute-Semigroup x y z H =
    ( associative-mul-Semigroup G _ _ _) ∙
    ( ap (x *_) H) ∙
    ( inv (associative-mul-Semigroup G _ _ _))
```

### If `x` commutes with `y` and with `z`, then `x` commutes with `yz`

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  private
    infix 45 _*_
    _*_ = mul-Semigroup G

  commute-mul-Semigroup :
    (x y z : type-Semigroup G) →
    commute-Semigroup G x y → commute-Semigroup G x z →
    commute-Semigroup G x (mul-Semigroup G y z)
  commute-mul-Semigroup x y z H K =
    equational-reasoning
      (x * (y * z))
      ＝ y * (x * z) by left-swap-commute-Semigroup G _ _ _ H
      ＝ y * (z * x) by ap (y *_) K
      ＝ (y * z) * x by inv (associative-mul-Semigroup G _ _ _)
```
