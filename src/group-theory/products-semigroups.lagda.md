# Products of semigroups

```agda
module group-theory.products-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universe-levels

open import group-theory.isomorphisms-semigroups
open import group-theory.semigroups
```

</details>

## Idea

Given a pair of [semigroups](group-theory.semigroups.md) `G` and `H`, the
{{#concept "product" disambiguation="of semigroups" Agda=product-Semigroup}}
`G × H` consists of pairs of elements of G and H with the pairwise binary
operation.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  type-product-Semigroup : UU (l1 ⊔ l2)
  type-product-Semigroup = type-Semigroup G × type-Semigroup H

  set-product-Semigroup : Set (l1 ⊔ l2)
  set-product-Semigroup = product-Set (set-Semigroup G) (set-Semigroup H)

  mul-product-Semigroup :
    type-product-Semigroup → type-product-Semigroup → type-product-Semigroup
  mul-product-Semigroup (g1 , h1) (g2 , h2) =
    (mul-Semigroup G g1 g2 , mul-Semigroup H h1 h2)

  associative-mul-product-Semigroup :
    (x y z : type-product-Semigroup) →
    mul-product-Semigroup (mul-product-Semigroup x y) z ＝
    mul-product-Semigroup x (mul-product-Semigroup y z)
  associative-mul-product-Semigroup _ _ _ =
    eq-pair
      ( associative-mul-Semigroup G _ _ _)
      ( associative-mul-Semigroup H _ _ _)

  product-Semigroup : Semigroup (l1 ⊔ l2)
  product-Semigroup =
    set-product-Semigroup ,
    mul-product-Semigroup ,
    associative-mul-product-Semigroup
```

### Commutativity of products of semigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  commutative-product-Semigroup :
    iso-Semigroup
      ( product-Semigroup G H)
      ( product-Semigroup H G)
  commutative-product-Semigroup =
    iso-equiv-Semigroup
      ( product-Semigroup G H)
      ( product-Semigroup H G)
      ( commutative-product , refl)
```
