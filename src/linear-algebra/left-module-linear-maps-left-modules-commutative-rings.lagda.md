# The left module of linear maps between left modules over commutative rings

```agda
module linear-algebra.left-module-linear-maps-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.addition-linear-maps-left-modules-commutative-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
open import linear-algebra.scalar-multiplication-linear-maps-left-modules-commutative-rings
```

</details>

## Idea

The type of
[linear maps](linear-algebra.linear-maps-left-modules-commutative-rings.md)
between two [left modules](linear-algebra.left-modules-commutative-rings.md)
over the same [commutative ring](commutative-algebra.commutative-rings.md) `R`
itself forms a left module over `R`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  where

  left-module-linear-map-left-module-Commutative-Ring :
    left-module-Commutative-Ring (l1 ⊔ l2 ⊔ l3) R
  left-module-linear-map-left-module-Commutative-Ring =
    make-left-module-Commutative-Ring
      ( R)
      ( ab-add-linear-map-left-module-Commutative-Ring R M N)
      ( mul-linear-map-left-module-Commutative-Ring R M N)
      ( left-distributive-mul-add-linear-map-left-module-Commutative-Ring R M N)
      ( right-distributive-mul-add-linear-map-left-module-Commutative-Ring
        ( R)
        ( M)
        ( N))
      ( left-unit-law-mul-linear-map-left-module-Commutative-Ring R M N)
      ( associative-mul-linear-map-left-module-Commutative-Ring R M N)
```

## Properties

### Evaluation of a linear map is a linear map

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  (x : type-left-module-Commutative-Ring R M)
  where

  is-linear-ev-linear-map-left-module-Commutative-Ring :
    is-linear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-linear-map-left-module-Commutative-Ring R M N)
      ( N)
      ( ev-linear-map-left-module-Commutative-Ring R M N x)
  is-linear-ev-linear-map-left-module-Commutative-Ring =
    ( ( λ _ _ → refl) ,
      ( λ _ _ → refl))

  linear-map-ev-linear-map-left-module-Commutative-Ring :
    linear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-linear-map-left-module-Commutative-Ring R M N)
      ( N)
  linear-map-ev-linear-map-left-module-Commutative-Ring =
    ( ev-linear-map-left-module-Commutative-Ring R M N x ,
      is-linear-ev-linear-map-left-module-Commutative-Ring)
```

## See also

- [Duals of left modules over commutative rings](linear-algebra.duals-left-modules-commutative-rings.md),
  a special case of this module
