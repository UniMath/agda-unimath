# Intersections of subgroups of groups

```agda
module group-theory.intersections-subgroups-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.intersections-subtypes
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.subgroups
open import group-theory.subsets-groups

open import order-theory.greatest-lower-bounds-large-posets
```

</details>

## Idea

The **intersection** of two subgroups `H, K ≤ G` is again closed under the group
operations, and is therefore a subgroup of `G`.

## Definitions

### The intersection of two subgroups

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Subgroup l2 G) (K : Subgroup l3 G)
  where

  subset-intersection-Subgroup :
    subset-Group (l2 ⊔ l3) G
  subset-intersection-Subgroup =
    intersection-subtype (subset-Subgroup G H) (subset-Subgroup G K)

  is-in-intersection-Subgroup :
    type-Group G → UU (l2 ⊔ l3)
  is-in-intersection-Subgroup =
    is-in-subtype subset-intersection-Subgroup

  contains-unit-intersection-Subgroup :
    is-in-intersection-Subgroup (unit-Group G)
  pr1 contains-unit-intersection-Subgroup = contains-unit-Subgroup G H
  pr2 contains-unit-intersection-Subgroup = contains-unit-Subgroup G K

  is-closed-under-multiplication-intersection-Subgroup :
    (x y : type-Group G) →
    is-in-intersection-Subgroup x →
    is-in-intersection-Subgroup y →
    is-in-intersection-Subgroup (mul-Group G x y)
  pr1
    ( is-closed-under-multiplication-intersection-Subgroup
        x y (pH , pK) (qH , qK)) =
    is-closed-under-multiplication-Subgroup G H x y pH qH
  pr2
    ( is-closed-under-multiplication-intersection-Subgroup
        x y (pH , pK) (qH , qK)) =
    is-closed-under-multiplication-Subgroup G K x y pK qK

  is-closed-under-inv-intersection-Subgroup :
    (x : type-Group G) →
    is-in-intersection-Subgroup x → is-in-intersection-Subgroup (inv-Group G x)
  pr1 (is-closed-under-inv-intersection-Subgroup x (pH , pK)) =
    is-closed-under-inv-Subgroup G H x pH
  pr2 (is-closed-under-inv-intersection-Subgroup x (pH , pK)) =
    is-closed-under-inv-Subgroup G K x pK

  is-subgroup-intersection-Subgroup :
    is-subgroup-subset-Group G subset-intersection-Subgroup
  pr1 is-subgroup-intersection-Subgroup =
    contains-unit-intersection-Subgroup
  pr1 (pr2 is-subgroup-intersection-Subgroup) =
    is-closed-under-multiplication-intersection-Subgroup
  pr2 (pr2 is-subgroup-intersection-Subgroup) =
    is-closed-under-inv-intersection-Subgroup

  intersection-Subgroup : Subgroup (l2 ⊔ l3) G
  pr1 intersection-Subgroup = subset-intersection-Subgroup
  pr2 intersection-Subgroup = is-subgroup-intersection-Subgroup
```

## Properties

### The intersection of `H` and `K` is the greatest binary lower bound of `H` and `K` in the poset of subgroups of `G`

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Subgroup l2 G) (K : Subgroup l3 G)
  where

  is-greatest-binary-lower-bound-intersection-Subgroup :
    is-greatest-binary-lower-bound-Large-Poset
      ( Subgroup-Large-Poset G)
      ( H)
      ( K)
      ( intersection-Subgroup G H K)
  is-greatest-binary-lower-bound-intersection-Subgroup L =
    is-greatest-binary-lower-bound-intersection-subtype
      ( subset-Subgroup G H)
      ( subset-Subgroup G K)
      ( subset-Subgroup G L)
```
