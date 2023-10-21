# Homomorphisms of groups equipped with normal subgroups

```agda
module group-theory.homomorphisms-groups-equipped-with-normal-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.normal-subgroups
```

</details>

## Idea

Consider a [group](group-theory.groups.md) `G` equipped with a
[normal subgroup](group-theory.normal-subgroups.md) and a group `H` equipped
with a normal subgroup `M`. A **homomorphism of groups equipped with normal
subgroups** from `(G,N)` to `(H,M)` consists of a
[group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H` which
**reflects** the normal subgroup `N` into `M`, i.e., such that the condition
`x ∈ N ⇒ f x ∈ M` holds.

## Definitions

### The property of group homomorphisms of reflecting a normal subgroup

We say that a group homomorphism `f : G → H` **reflects** a normal subgroup `N`
of `G` into a normal subgroup `M` of `H` if the property

```text
  x ∈ N ⇒ f x ∈ M
```

holds for every `x : G`, i.e., if `f` maps elements in `N` to elements in `M`.

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Group l2)
  (N : Normal-Subgroup l3 G) (M : Normal-Subgroup l4 H)
  where

  reflects-normal-subgroup-hom-Group : hom-Group G H → UU (l1 ⊔ l3 ⊔ l4)
  reflects-normal-subgroup-hom-Group f =
    (x : type-Group G) → is-in-Normal-Subgroup G N x →
    is-in-Normal-Subgroup H M (map-hom-Group G H f x)

  reflecting-hom-Group : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  reflecting-hom-Group = Σ (hom-Group G H) reflects-normal-subgroup-hom-Group

module _
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Group l2)
  (N : Normal-Subgroup l3 G) (M : Normal-Subgroup l4 H)
  (f : reflecting-hom-Group G H N M)
  where

  hom-reflecting-hom-Group : hom-Group G H
  hom-reflecting-hom-Group = pr1 f

  reflects-normal-subgroup-reflecting-hom-Group :
    reflects-normal-subgroup-hom-Group G H N M hom-reflecting-hom-Group
  reflects-normal-subgroup-reflecting-hom-Group = pr2 f

  map-reflecting-hom-Group : type-Group G → type-Group H
  map-reflecting-hom-Group = map-hom-Group G H hom-reflecting-hom-Group
```
