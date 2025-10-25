# Cartesian products of semigroups

```agda
module group-theory.cartesian-products-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

The
{{#concept "cartesian product" disambiguation="of semigroups" Agda=product-Semigroup WDID=Q173740 WD="Cartesian product"}}
of two [semigroups](group-theory.semigroups.md) `G` and `H` consists of the
[product](foundation.cartesian-product-types.md) `G × H` of the underlying
[sets](foundation.sets.md) and the componentwise operation on it.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Semigroup l1) (B : Semigroup l2)
  where

  set-product-Semigroup : Set (l1 ⊔ l2)
  set-product-Semigroup = product-Set (set-Semigroup A) (set-Semigroup B)

  type-product-Semigroup : UU (l1 ⊔ l2)
  type-product-Semigroup = type-Set set-product-Semigroup

  is-set-type-product-Semigroup : is-set type-product-Semigroup
  is-set-type-product-Semigroup = is-set-type-Set set-product-Semigroup

  mul-product-Semigroup :
    type-product-Semigroup → type-product-Semigroup → type-product-Semigroup
  pr1 (mul-product-Semigroup (pair x1 y1) (pair x2 y2)) = mul-Semigroup A x1 x2
  pr2 (mul-product-Semigroup (pair x1 y1) (pair x2 y2)) = mul-Semigroup B y1 y2

  associative-mul-product-Semigroup :
    (x y z : type-product-Semigroup) →
    mul-product-Semigroup (mul-product-Semigroup x y) z ＝
    mul-product-Semigroup x (mul-product-Semigroup y z)
  associative-mul-product-Semigroup (pair x1 y1) (pair x2 y2) (pair x3 y3) =
    eq-pair
      ( associative-mul-Semigroup A x1 x2 x3)
      ( associative-mul-Semigroup B y1 y2 y3)

  product-Semigroup : Semigroup (l1 ⊔ l2)
  pr1 product-Semigroup = set-product-Semigroup
  pr1 (pr2 product-Semigroup) = mul-product-Semigroup
  pr2 (pr2 product-Semigroup) = associative-mul-product-Semigroup
```
