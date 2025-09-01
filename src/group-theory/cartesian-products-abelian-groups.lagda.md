# Cartesian products of abelian groups

```agda
module group-theory.cartesian-products-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.cartesian-products-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The
{{#concept "cartesian product" disambiguation="of abelian groups" Agda=product-Ab WDID=Q173740 WD="Cartesian product"}}
of two [abelian groups](group-theory.abelian-groups.md) `A` and `B` is the
abelian group structure on the
[cartesian product](foundation.cartesian-product-types.md) of the underlying
[sets](foundation.sets.md) given by

```text
  (a , b) * (a' , b') := (a * a' , b * b').
```

## Definition

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  group-product-Ab : Group (l1 ⊔ l2)
  group-product-Ab = product-Group (group-Ab A) (group-Ab B)

  monoid-product-Ab : Monoid (l1 ⊔ l2)
  monoid-product-Ab = monoid-Group group-product-Ab

  semigroup-product-Ab : Semigroup (l1 ⊔ l2)
  semigroup-product-Ab = semigroup-Group group-product-Ab

  set-product-Ab : Set (l1 ⊔ l2)
  set-product-Ab = set-Group group-product-Ab

  type-product-Ab : UU (l1 ⊔ l2)
  type-product-Ab = type-Group group-product-Ab

  is-set-type-product-Ab : is-set type-product-Ab
  is-set-type-product-Ab = is-set-type-Group group-product-Ab

  add-product-Ab : (x y : type-product-Ab) → type-product-Ab
  add-product-Ab = mul-Group group-product-Ab

  zero-product-Ab : type-product-Ab
  zero-product-Ab = unit-Group group-product-Ab

  neg-product-Ab : type-product-Ab → type-product-Ab
  neg-product-Ab = inv-Group group-product-Ab

  associative-add-product-Ab :
    (x y z : type-product-Ab) →
    Id
      ( add-product-Ab (add-product-Ab x y) z)
      ( add-product-Ab x (add-product-Ab y z))
  associative-add-product-Ab = associative-mul-Group group-product-Ab

  left-unit-law-add-product-Ab :
    (x : type-product-Ab) → add-product-Ab zero-product-Ab x ＝ x
  left-unit-law-add-product-Ab = left-unit-law-mul-Group group-product-Ab

  right-unit-law-add-product-Ab :
    (x : type-product-Ab) → add-product-Ab x zero-product-Ab ＝ x
  right-unit-law-add-product-Ab = right-unit-law-mul-Group group-product-Ab

  left-inverse-law-add-product-Ab :
    (x : type-product-Ab) →
    add-product-Ab (neg-product-Ab x) x ＝ zero-product-Ab
  left-inverse-law-add-product-Ab = left-inverse-law-mul-Group group-product-Ab

  right-inverse-law-add-product-Ab :
    (x : type-product-Ab) →
    add-product-Ab x (neg-product-Ab x) ＝ zero-product-Ab
  right-inverse-law-add-product-Ab =
    right-inverse-law-mul-Group group-product-Ab

  commutative-add-product-Ab :
    (x y : type-product-Ab) → add-product-Ab x y ＝ add-product-Ab y x
  commutative-add-product-Ab (pair x1 y1) (pair x2 y2) =
    eq-pair (commutative-add-Ab A x1 x2) (commutative-add-Ab B y1 y2)

  product-Ab : Ab (l1 ⊔ l2)
  pr1 product-Ab = group-product-Ab
  pr2 product-Ab = commutative-add-product-Ab
```
