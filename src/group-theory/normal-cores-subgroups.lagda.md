# Normal cores of subgroups

```agda
module group-theory.normal-cores-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.intersections-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-maps
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.conjugation
open import group-theory.groups
open import group-theory.normal-subgroups
open import group-theory.subgroups
open import group-theory.subsets-groups
```

</details>

## Idea

Consider a [subgroup](group-theory.subgroups.md) `H` of a
[group](group-theory.groups.md) `G`. The **normal core** of `H` is the largest
[normal subgroup](group-theory.normal-subgroups.md) of `G` that is contained in
`H`. It is equivalently described as the intersection of all
[conjugates](group-theory.conjugation.md) of `H`.

In other words, the normal core operation is the upper adjoint in a
[Galois connection](order-theory.galois-connections-large-posets.md) between the
[large poset](order-theory.large-posets.md) of subgroups of `G` and normal
subgroups of `G`. The lower adjoint of this Galois connection is the inclusion
function from normal subgroups to subgroups of `G`.

Note: The normal core should not be confused with the
[normalizer](group-theory.normalizer-subgroups.md) of a subgroup, or with the
[normal closure](group-theory.normal-closures-subgroups.md) of a subgroup.

## Definitions

### The universal property of the normal core

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  is-normal-core-Subgroup :
    {l3 : Level} (N : Normal-Subgroup l3 G) → UUω
  is-normal-core-Subgroup N =
    {l : Level} (M : Normal-Subgroup l G) →
    leq-Subgroup G (subgroup-Normal-Subgroup G M) H ↔ leq-Normal-Subgroup G N M
```

### The construction of the normal core

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  subset-normal-core-Subgroup : subset-Group (l1 ⊔ l2) G
  subset-normal-core-Subgroup =
    intersection-family-of-subtypes
      ( λ (x : type-Group G) →
        fib-emb-Prop
          ( comp-emb
            ( emb-equiv (equiv-conjugation-Group G x))
            ( emb-inclusion-Subgroup G H)))

  is-in-normal-core-Subgroup : type-Group G → UU (l1 ⊔ l2)
  is-in-normal-core-Subgroup =
    is-in-subtype subset-normal-core-Subgroup

  is-closed-under-eq-normal-core-Subgroup :
    {x y : type-Group G} → is-in-normal-core-Subgroup x →
    x ＝ y → is-in-normal-core-Subgroup y
  is-closed-under-eq-normal-core-Subgroup =
    is-closed-under-eq-subtype subset-normal-core-Subgroup

  is-closed-under-eq-normal-core-Subgroup' :
    {x y : type-Group G} → is-in-normal-core-Subgroup y →
    x ＝ y → is-in-normal-core-Subgroup x
  is-closed-under-eq-normal-core-Subgroup' =
    is-closed-under-eq-subtype' subset-normal-core-Subgroup

  contains-unit-normal-core-Subgroup :
    contains-unit-subset-Group G subset-normal-core-Subgroup
  pr1 (contains-unit-normal-core-Subgroup x) = unit-Subgroup G H
  pr2 (contains-unit-normal-core-Subgroup x) = conjugation-unit-Group G x

  is-closed-under-multiplication-normal-core-Subgroup :
    is-closed-under-multiplication-subset-Group G subset-normal-core-Subgroup
  pr1 (is-closed-under-multiplication-normal-core-Subgroup x y u v z) =
    mul-Subgroup G H (pr1 (u z)) (pr1 (v z))
  pr2 (is-closed-under-multiplication-normal-core-Subgroup x y u v z) =
    ( distributive-conjugation-mul-Group G z
      ( inclusion-Subgroup G H (pr1 (u z)))
      ( inclusion-Subgroup G H (pr1 (v z)))) ∙
    ( ap-mul-Group G (pr2 (u z)) (pr2 (v z)))

  is-closed-under-inv-normal-core-Subgroup :
    is-closed-under-inv-subset-Group G subset-normal-core-Subgroup
  pr1 (is-closed-under-inv-normal-core-Subgroup x u z) =
    inv-Subgroup G H (pr1 (u z))
  pr2 (is-closed-under-inv-normal-core-Subgroup x u z) =
    ( conjugation-inv-Group G z (inclusion-Subgroup G H (pr1 (u z)))) ∙
    ( ap (inv-Group G) (pr2 (u z)))

  subgroup-normal-core-Subgroup : Subgroup (l1 ⊔ l2) G
  pr1 subgroup-normal-core-Subgroup =
    subset-normal-core-Subgroup
  pr1 (pr2 subgroup-normal-core-Subgroup) =
    contains-unit-normal-core-Subgroup
  pr1 (pr2 (pr2 subgroup-normal-core-Subgroup)) =
    is-closed-under-multiplication-normal-core-Subgroup
  pr2 (pr2 (pr2 subgroup-normal-core-Subgroup)) =
    is-closed-under-inv-normal-core-Subgroup
```

## See also

- [Centralizer subgroups](group-theory.centralizer-subgroups.md)
- [Normal closures of subgroups](group-theory.normal-closures-subgroups.md)
- [Normalizers of subgroups](group-theory.normalizer-subgroups.md)
