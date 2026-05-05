# The order of an element in a group

```agda
module group-theory.orders-of-elements-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.integers

open import foundation.universe-levels

open import group-theory.free-groups-with-one-generator
open import group-theory.groups
open import group-theory.kernels-homomorphisms-groups
open import group-theory.normal-subgroups
open import group-theory.subgroups
open import group-theory.subsets-groups
```

</details>

## Idea

For each element `g : G` of a group `G` we have a unique group homomorphism
`f : ℤ → G` such that `f 1 = g`. The
{{#concept "order" WD="order of a group element" WDID=Q54555759 Agda=order-element-Group}}
of `g` is defined to be the kernel of this group homomorphism `f`. Since kernels
are ordered by inclusion, it follows that the orders of elements of a group are
ordered by reversed inclusion.

If the group `G` has decidable equality, then we can reduce the order of `g` to
a natural number. In this case, the orders of elements of `G` are ordered by
divisibility.

If the unique group homomorphism `f : ℤ → G` such that `f 1 = g` is injective,
and `G` has decidable equality, then the order of `g` is set to be `0`, which is
a consequence of the point of view that orders are normal subgroups of `ℤ`.

## Definitions

### The order of an element in a group

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  order-element-Group : Normal-Subgroup l ℤ-Group
  order-element-Group =
    kernel-hom-Group ℤ-Group G (hom-element-Group G g)

  subgroup-order-element-Group : Subgroup l ℤ-Group
  subgroup-order-element-Group =
    subgroup-kernel-hom-Group ℤ-Group G (hom-element-Group G g)

  subset-order-element-Group : subset-Group l ℤ-Group
  subset-order-element-Group =
    subset-kernel-hom-Group ℤ-Group G (hom-element-Group G g)

  is-in-order-element-Group : ℤ → UU l
  is-in-order-element-Group =
    is-in-kernel-hom-Group ℤ-Group G (hom-element-Group G g)
```

### Divisibility of orders of elements of a group

We say that the order of `x` divides the order of `y` if the normal subgroup
`order-element-Group G y` is contained in the normal subgroup
`order-elemetn-Group G x`. In other words, the order of `x` divides the order of
`y` if for every integer `k` such that `yᵏ ＝ e` we have `xᵏ ＝ e`.

```agda
module _
  {l : Level} (G : Group l)
  where

  div-order-element-Group : (x y : type-Group G) → UU l
  div-order-element-Group x y =
    leq-Normal-Subgroup
      ( ℤ-Group)
      ( order-element-Group G y)
      ( order-element-Group G x)
```
