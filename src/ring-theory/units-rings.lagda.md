# Unit elements in rings

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module ring-theory.units-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

A **unit element** of a [ring](ring-theory.rings.md) `R` is an element `u : R`
for which there exists an element `v` such that `uv ＝ 1` and `vu ＝ 1`.

## Definitions

### The group of units in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-unit-Ring : type-Ring R → UU l
  is-unit-Ring x =
    Σ ( type-Ring R)
      ( λ y →
        ( mul-Ring R x y ＝ one-Ring R) ×
        ( mul-Ring R y x ＝ one-Ring R))

  all-elements-equal-is-unit-Ring :
    (x : type-Ring R) →
    all-elements-equal (is-unit-Ring x)
  all-elements-equal-is-unit-Ring x (y , H) (z , K) =
    eq-type-subtype
      ( λ y →
        prod-Prop
          ( Id-Prop
            ( set-Ring R)
            ( mul-Ring R x y)
            ( one-Ring R))
          ( Id-Prop
            ( set-Ring R)
            ( mul-Ring R y x)
            ( one-Ring R)))
      ( equational-reasoning
        y
        ＝ mul-Ring R y (one-Ring R)
          by
          inv (right-unit-law-mul-Ring R y)
        ＝ mul-Ring R y (mul-Ring R x z)
          by ap (mul-Ring R y) (inv (pr1 K))
        ＝ mul-Ring R (mul-Ring R y x) z
          by inv (associative-mul-Ring R y x z)
        ＝ mul-Ring R (one-Ring R) z
          by ap (mul-Ring' R z) (pr2 H)
        ＝ z
          by left-unit-law-mul-Ring R z)

  is-prop-is-unit-Ring :
    (x : type-Ring R) → is-prop (is-unit-Ring x)
  is-prop-is-unit-Ring x =
    is-prop-all-elements-equal
      ( all-elements-equal-is-unit-Ring x)

  is-unit-Ring-Prop : type-Ring R → Prop l
  pr1 (is-unit-Ring-Prop x) = is-unit-Ring x
  pr2 (is-unit-Ring-Prop x) = is-prop-is-unit-Ring x

  unit-Ring : UU l
  unit-Ring = Σ (type-Ring R) is-unit-Ring
```

### Group operations on the type of units of a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-unit-mul-Ring :
    (x y : type-Ring R) →
    is-unit-Ring R x → is-unit-Ring R y →
    is-unit-Ring R (mul-Ring R x y)
  pr1 (is-unit-mul-Ring x y (x⁻¹ , p , q) (y⁻¹ , r , s)) =
    mul-Ring R y⁻¹ x⁻¹
  pr1 (pr2 (is-unit-mul-Ring x y (x⁻¹ , p , q) (y⁻¹ , r , s))) =
    ( associative-mul-Ring R x y (mul-Ring R y⁻¹ x⁻¹)) ∙
    ( ( ap
        ( mul-Ring R x)
        ( ( inv (associative-mul-Ring R y y⁻¹ x⁻¹)) ∙
          ( ( ap (mul-Ring' R x⁻¹) r) ∙
            ( left-unit-law-mul-Ring R x⁻¹)))) ∙
      ( p))
  pr2 (pr2 (is-unit-mul-Ring x y (x⁻¹ , p , q) (y⁻¹ , r , s))) =
    {!!}
```
