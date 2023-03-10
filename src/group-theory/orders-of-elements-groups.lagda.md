# The order of an element in a group

```agda
module group-theory.orders-of-elements-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integers

open import foundation.universe-levels

open import group-theory.free-groups-with-one-generator
open import group-theory.groups
open import group-theory.kernels
open import group-theory.normal-subgroups
```

</details>

## Idea

For each element `g : G` of a group `G` we have a unique group homomorphism `f : ℤ → G` such that `f 1 = g`. The order of `g` is defined to be the kernel of this group homomorphism `f`. Since kernels are ordered by inclusion, it follows that the orders of elements of a group are ordered by reversed inclusion.

If the group `G` has decidable equality, then we can reduce the order of `g` to a natural number. In this case, the orders of elements of `G` are ordered by divisibility.

If the unique group homomorphism `f : ℤ → G` such that `f 1 = g` is injective, and `G` has decidable equality, then the order of `g` is set to be `0`, which is a consequence of the point of view that orders are normal subgroups of `ℤ`.

## Definitions

### The type of orders of elements in groups

```agda
order-Group : (l : Level) → UU (lsuc l)
order-Group l = Normal-Subgroup l ℤ-Group
```

### The order of an element in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  order-element-Group : type-Group G → order-Group l
  order-element-Group g =
    kernel-hom-Group ℤ-Group G (hom-free-group-with-one-generator-ℤ G g)
```
