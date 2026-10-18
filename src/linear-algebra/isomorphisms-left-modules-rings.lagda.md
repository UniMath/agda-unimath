# Isomorphisms of left modules over rings

```agda
module linear-algebra.isomorphisms-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings
open import linear-algebra.precategory-of-left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

{{#concept "Isomorphisms" Disambiguation="of left modules over a ring" Agda=iso-left-module-Ring}}
of [left modules](linear-algebra.left-modules-rings.md) over a
[ring](ring-theory.rings.md) are
[linear maps](linear-algebra.linear-maps-left-modules-rings.md) that have a
two-sided inverse.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  where

  is-iso-prop-left-module-Ring :
    subtype (l1 ⊔ l2 ⊔ l3) (linear-map-left-module-Ring R M N)
  is-iso-prop-left-module-Ring =
    is-iso-prop-Large-Precategory
      ( large-precategory-left-module-Ring R)
      { X = M}
      { Y = N}

  is-iso-left-module-Ring :
    linear-map-left-module-Ring R M N → UU (l1 ⊔ l2 ⊔ l3)
  is-iso-left-module-Ring = is-in-subtype is-iso-prop-left-module-Ring

  iso-left-module-Ring : UU (l1 ⊔ l2 ⊔ l3)
  iso-left-module-Ring = type-subtype is-iso-prop-left-module-Ring

  linear-map-iso-left-module-Ring :
    iso-left-module-Ring → linear-map-left-module-Ring R M N
  linear-map-iso-left-module-Ring = pr1

  is-iso-linear-map-iso-left-module-Ring :
    (i : iso-left-module-Ring) →
    is-iso-left-module-Ring (linear-map-iso-left-module-Ring i)
  is-iso-linear-map-iso-left-module-Ring = pr2

  map-iso-left-module-Ring :
    iso-left-module-Ring → type-left-module-Ring R M → type-left-module-Ring R N
  map-iso-left-module-Ring i =
    map-linear-map-left-module-Ring R M N (linear-map-iso-left-module-Ring i)

module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (f : iso-left-module-Ring R M N)
  where

  inv-iso-left-module-Ring : iso-left-module-Ring R N M
  inv-iso-left-module-Ring =
    inv-iso-Large-Precategory
      ( large-precategory-left-module-Ring R)
      { X = M}
      { Y = N}
      ( f)

  linear-map-inv-iso-left-module-Ring : linear-map-left-module-Ring R N M
  linear-map-inv-iso-left-module-Ring =
    linear-map-iso-left-module-Ring R N M inv-iso-left-module-Ring

  map-inv-iso-left-module-Ring :
    type-left-module-Ring R N → type-left-module-Ring R M
  map-inv-iso-left-module-Ring =
    map-linear-map-left-module-Ring R N M linear-map-inv-iso-left-module-Ring
```
