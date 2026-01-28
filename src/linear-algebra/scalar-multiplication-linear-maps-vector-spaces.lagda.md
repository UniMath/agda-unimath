# Scalar multiplication of linear maps between vector spaces

```agda
module linear-algebra.scalar-multiplication-linear-maps-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.universe-levels

open import linear-algebra.linear-maps-vector-spaces
open import linear-algebra.linear-transformations-vector-spaces
open import linear-algebra.scalar-multiplication-linear-maps-left-modules-commutative-rings
open import linear-algebra.vector-spaces
```

</details>

## Idea

Given a [linear map](linear-algebra.linear-maps-vector-spaces.md) `f` from a
[vector space](linear-algebra.vector-spaces.md) `V` to another vector space `W`
and a constant `c : R`, the map `x ↦ c * f x` is a linear map.

## Definition

### The linear transformation of scalar multiplication

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (c : type-Heyting-Field F)
  where

  is-linear-map-mul-Vector-Space :
    is-linear-transform-Vector-Space F V (mul-Vector-Space F V c)
  is-linear-mul-Vector-Space =
    is-linear-mul-left-module-Commutative-Ring
      ( commutative-ring-Heyting-Field F)
      ( V)
      ( c)

  linear-transform-mul-Vector-Space : linear-transform-Vector-Space F V
  linear-transform-mul-Vector-Space =
    linear-transform-mul-left-module-Commutative-Ring
      ( commutative-ring-Heyting-Field F)
      ( V)
      ( c)
```

### Scalar multiplication of linear maps

```agda
module _
  {l1 l2 l3 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (W : Vector-Space l3 F)
  (c : type-Heyting-Field F)
  where

  mul-linear-map-Vector-Space :
    linear-map-Vector-Space F V W → linear-map-Vector-Space F V W
  mul-linear-map-Vector-Space =
    comp-linear-map-Vector-Space F V W W
      ( linear-transform-mul-Vector-Space F W c)
```
