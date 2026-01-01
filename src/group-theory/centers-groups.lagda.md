# The center of a group

```agda
module group-theory.centers-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.centers-monoids
open import group-theory.central-elements-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.normal-subgroups
open import group-theory.subgroups
```

</details>

## Idea

The
{{#concept "center" Disambiguation="of a group" WDID=Q1195852 WD="center" Agda=center-Group}}
of a [group](group-theory.groups.md) `G` is the
[abelian](group-theory.abelian-groups.md)
[normal](group-theory.normal-subgroups.md) [subgroup](group-theory.subgroups.md)
consisting of those elements that are
[central](group-theory.central-elements-groups.md) in `G`.

## Definition

```agda
module _
  {l : Level} (G : Group l)
  where

  subtype-center-Group : type-Group G → Prop l
  subtype-center-Group = is-central-element-prop-Group G

  subgroup-center-Group : Subgroup l G
  pr1 subgroup-center-Group =
    subtype-center-Group
  pr1 (pr2 subgroup-center-Group) =
    is-central-element-unit-Group G
  pr1 (pr2 (pr2 subgroup-center-Group)) =
    is-central-element-mul-Group G
  pr2 (pr2 (pr2 subgroup-center-Group)) =
    is-central-element-inv-Group G

  group-center-Group : Group l
  group-center-Group = group-Subgroup G subgroup-center-Group

  type-center-Group : UU l
  type-center-Group =
    type-Subgroup G subgroup-center-Group

  mul-center-Group :
    (x y : type-center-Group) → type-center-Group
  mul-center-Group = mul-Subgroup G subgroup-center-Group

  associative-mul-center-Group :
    (x y z : type-center-Group) →
    mul-center-Group (mul-center-Group x y) z ＝
    mul-center-Group x (mul-center-Group y z)
  associative-mul-center-Group =
    associative-mul-Subgroup G subgroup-center-Group

  inclusion-center-Group :
    type-center-Group → type-Group G
  inclusion-center-Group =
    inclusion-Subgroup G subgroup-center-Group

  is-central-element-inclusion-center-Group :
    (x : type-center-Group) →
    is-central-element-Group G (inclusion-center-Group x)
  is-central-element-inclusion-center-Group x =
    is-in-subgroup-inclusion-Subgroup G subgroup-center-Group x

  preserves-mul-inclusion-center-Group :
    {x y : type-center-Group} →
    inclusion-center-Group (mul-center-Group x y) ＝
    mul-Group G
      ( inclusion-center-Group x)
      ( inclusion-center-Group y)
  preserves-mul-inclusion-center-Group {x} {y} =
    preserves-mul-inclusion-Subgroup G subgroup-center-Group {x} {y}

  hom-inclusion-center-Group :
    hom-Group group-center-Group G
  hom-inclusion-center-Group =
    hom-inclusion-Subgroup G subgroup-center-Group

  is-normal-subgroup-center-Group :
    is-normal-Subgroup G subgroup-center-Group
  is-normal-subgroup-center-Group x y =
    is-central-element-conjugation-Group G
      ( inclusion-center-Group y)
      ( x)
      ( is-central-element-inclusion-center-Group y)

  center-Group : Normal-Subgroup l G
  pr1 center-Group = subgroup-center-Group
  pr2 center-Group = is-normal-subgroup-center-Group

  abstract
    commutative-mul-center-Group :
      (x y : type-center-Group) →
      mul-center-Group x y ＝ mul-center-Group y x
    commutative-mul-center-Group =
      commutative-mul-center-Monoid (monoid-Group G)

  ab-center-Group : Ab l
  ab-center-Group =
    ( group-center-Group ,
      commutative-mul-center-Group)
```

## External links

- [Center (group theory)](<https://en.wikipedia.org/wiki/Center_(group_theory)>)
  on Wikipedia
