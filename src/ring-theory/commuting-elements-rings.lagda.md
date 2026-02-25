# Commuting elements of rings

```agda
module ring-theory.commuting-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.commuting-elements-monoids

open import ring-theory.rings
```

</details>

## Idea

Two elements `x` and `y` of a [ring](ring-theory.rings.md) `R` are said to
{{#concept "commute" Disambiguation="pair of elements of a ring" Agda=commute-Ring}}
if `xy ＝ yx`.

## Definitions

### Commuting elements

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-prop-Ring : (x y : type-Ring R) → Prop l
  commute-prop-Ring = commute-prop-Monoid (multiplicative-monoid-Ring R)

  commute-Ring : (x y : type-Ring R) → UU l
  commute-Ring = commute-Monoid (multiplicative-monoid-Ring R)

  commute-Ring' : (x y : type-Ring R) → UU l
  commute-Ring' = commute-Monoid' (multiplicative-monoid-Ring R)

  is-prop-commute-Ring : (x y : type-Ring R) → is-prop (commute-Ring x y)
  is-prop-commute-Ring = is-prop-commute-Monoid (multiplicative-monoid-Ring R)
```

## Properties

### The relation `commute-Ring` is reflexive

```agda
module _
  {l : Level} (R : Ring l)
  where

  refl-commute-Ring : (x : type-Ring R) → commute-Ring R x x
  refl-commute-Ring = refl-commute-Monoid (multiplicative-monoid-Ring R)
```

### The relation `commute-Ring` is symmetric

```agda
module _
  {l : Level} (R : Ring l)
  where

  symmetric-commute-Ring :
    (x y : type-Ring R) → commute-Ring R x y → commute-Ring R y x
  symmetric-commute-Ring =
    symmetric-commute-Monoid (multiplicative-monoid-Ring R)
```

### The zero element commutes with every element of the ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-zero-Ring : (x : type-Ring R) → commute-Ring R (zero-Ring R) x
  commute-zero-Ring x =
    left-zero-law-mul-Ring R x ∙ inv (right-zero-law-mul-Ring R x)
```

### The multiplicative unit element commutes with every element of the ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-one-Ring : (x : type-Ring R) → commute-Ring R x (one-Ring R)
  commute-one-Ring = commute-unit-Monoid (multiplicative-monoid-Ring R)
```

### If `y` and `z` commute with `x`, then `y + z` commutes with `x`

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-add-Ring :
    {x y z : type-Ring R} → commute-Ring R x y → commute-Ring R x z →
    commute-Ring R x (add-Ring R y z)
  commute-add-Ring H K =
    left-distributive-mul-add-Ring R _ _ _ ∙
    ap-add-Ring R H K ∙
    inv (right-distributive-mul-add-Ring R _ _ _)
```

### If `x` commutes with `y`, then `x` commutes with `-y`

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-neg-Ring :
    {x y : type-Ring R} → commute-Ring R x y → commute-Ring R x (neg-Ring R y)
  commute-neg-Ring H =
    right-negative-law-mul-Ring R _ _ ∙
    ap (neg-Ring R) H ∙
    inv (left-negative-law-mul-Ring R _ _)
```

### If `x` commutes with `y`, then `-x` commutes with `-y`

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-neg-neg-Ring :
    {x y : type-Ring R} → commute-Ring R x y →
    commute-Ring R (neg-Ring R x) (neg-Ring R y)
  commute-neg-neg-Ring H =
    mul-neg-Ring R _ _ ∙
    H ∙
    inv (mul-neg-Ring R _ _)
```

### If `x` commutes with `y` and `z`, then `x` commutes with `-y + z` and with `y - z`

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-left-subtraction-Ring :
    {x y z : type-Ring R} → commute-Ring R x y → commute-Ring R x z →
    commute-Ring R x (left-subtraction-Ring R y z)
  commute-left-subtraction-Ring H K =
    left-distributive-mul-left-subtraction-Ring R _ _ _ ∙
    ap-left-subtraction-Ring R H K ∙
    inv (right-distributive-mul-left-subtraction-Ring R _ _ _)

  commute-right-subtraction-Ring :
    {x y z : type-Ring R} → commute-Ring R x y → commute-Ring R x z →
    commute-Ring R x (right-subtraction-Ring R y z)
  commute-right-subtraction-Ring H K =
    left-distributive-mul-right-subtraction-Ring R _ _ _ ∙
    ap-right-subtraction-Ring R H K ∙
    inv (right-distributive-mul-right-subtraction-Ring R _ _ _)
```

### If `x` commutes with `y`, then `x * (y * z) ＝ y * (x * z)` for any element `z`

```agda
module _
  {l : Level} (R : Ring l)
  where

  private
    infix 50 _*_
    _*_ = mul-Ring R

  left-swap-commute-Ring :
    (x y z : type-Ring R) → commute-Ring R x y →
    x * (y * z) ＝ y * (x * z)
  left-swap-commute-Ring =
    left-swap-commute-Monoid (multiplicative-monoid-Ring R)

  right-swap-commute-Ring :
    (x y z : type-Ring R) → commute-Ring R y z →
    (x * y) * z ＝ (x * z) * y
  right-swap-commute-Ring =
    right-swap-commute-Monoid (multiplicative-monoid-Ring R)
```

### If `x` commutes with `y` and with `z`, then `x` commutes with `yz`

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-mul-Ring :
    (x y z : type-Ring R) →
    commute-Ring R x y → commute-Ring R x z →
    commute-Ring R x (mul-Ring R y z)
  commute-mul-Ring = commute-mul-Monoid (multiplicative-monoid-Ring R)
```
