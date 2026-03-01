# The full subgroup of a group

```agda
module group-theory.full-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-groups
open import group-theory.subgroups
open import group-theory.subsets-groups
```

</details>

## Idea

The **full subgroup** of a [group](group-theory.groups.md) `G` is the
[subgroup](group-theory.subgroups.md) consisting of all elements of the group
`G`. In other words, the full subgroup is the subgroup whose underlying subset
is the [full subset](foundation.full-subtypes.md) of the group.

## Definition

### Full subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  is-full-prop-Subgroup : Prop (l1 ⊔ l2)
  is-full-prop-Subgroup = is-full-prop-subtype (subset-Subgroup G H)

  is-full-Subgroup : UU (l1 ⊔ l2)
  is-full-Subgroup = type-Prop is-full-prop-Subgroup

  is-prop-is-full-Subgroup : is-prop is-full-Subgroup
  is-prop-is-full-Subgroup = is-prop-type-Prop is-full-prop-Subgroup
```

### The full subgroup at each universe level

```agda
subset-full-Subgroup :
  {l1 : Level} (l2 : Level) (G : Group l1) → subset-Group l2 G
subset-full-Subgroup l2 G = full-subtype l2 (type-Group G)

type-full-Subgroup :
  {l1 : Level} (l2 : Level) (G : Group l1) → UU (l1 ⊔ l2)
type-full-Subgroup l2 G = type-full-subtype l2 (type-Group G)

contains-unit-full-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  contains-unit-subset-Group G (subset-full-Subgroup l2 G)
contains-unit-full-Subgroup G = is-in-full-subtype (unit-Group G)

is-closed-under-multiplication-full-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  is-closed-under-multiplication-subset-Group G (subset-full-Subgroup l2 G)
is-closed-under-multiplication-full-Subgroup G {x} {y} _ _ =
  is-in-full-subtype (mul-Group G x y)

is-closed-under-inverses-full-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  is-closed-under-inverses-subset-Group G (subset-full-Subgroup l2 G)
is-closed-under-inverses-full-Subgroup G {x} _ =
  is-in-full-subtype (inv-Group G x)

full-Subgroup : {l1 : Level} (l2 : Level) (G : Group l1) → Subgroup l2 G
pr1 (full-Subgroup l2 G) =
  subset-full-Subgroup l2 G
pr1 (pr2 (full-Subgroup l2 G)) =
  contains-unit-full-Subgroup G
pr1 (pr2 (pr2 (full-Subgroup l2 G))) {x} {y} =
  is-closed-under-multiplication-full-Subgroup G {x} {y}
pr2 (pr2 (pr2 (full-Subgroup l2 G))) {x} =
  is-closed-under-inverses-full-Subgroup G {x}

module _
  {l1 l2 : Level} (G : Group l1)
  where

  inclusion-full-Subgroup : type-full-Subgroup l2 G → type-Group G
  inclusion-full-Subgroup = inclusion-Subgroup G (full-Subgroup l2 G)

  is-equiv-inclusion-full-Subgroup : is-equiv inclusion-full-Subgroup
  is-equiv-inclusion-full-Subgroup = is-equiv-inclusion-full-subtype

  equiv-inclusion-full-Subgroup : type-full-Subgroup l2 G ≃ type-Group G
  pr1 equiv-inclusion-full-Subgroup = inclusion-full-Subgroup
  pr2 equiv-inclusion-full-Subgroup = is-equiv-inclusion-full-Subgroup

  group-full-Subgroup : Group (l1 ⊔ l2)
  group-full-Subgroup = group-Subgroup G (full-Subgroup l2 G)

  hom-inclusion-full-Subgroup : hom-Group group-full-Subgroup G
  hom-inclusion-full-Subgroup =
    hom-inclusion-Subgroup G (full-Subgroup l2 G)

  preserves-mul-inclusion-full-Subgroup :
    preserves-mul-Group group-full-Subgroup G inclusion-full-Subgroup
  preserves-mul-inclusion-full-Subgroup {x} {y} =
    preserves-mul-inclusion-Subgroup G (full-Subgroup l2 G) {x} {y}

  equiv-group-inclusion-full-Subgroup : equiv-Group group-full-Subgroup G
  pr1 equiv-group-inclusion-full-Subgroup =
    equiv-inclusion-full-Subgroup
  pr2 equiv-group-inclusion-full-Subgroup {x} {y} =
    preserves-mul-inclusion-full-Subgroup {x} {y}

  iso-full-Subgroup : iso-Group group-full-Subgroup G
  iso-full-Subgroup =
    iso-equiv-Group group-full-Subgroup G equiv-group-inclusion-full-Subgroup

  inv-iso-full-Subgroup :
    iso-Group G group-full-Subgroup
  inv-iso-full-Subgroup =
    inv-iso-Group group-full-Subgroup G iso-full-Subgroup
```

## Properties

### A subgroup is full if and only if the inclusion is an isomorphism

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  is-iso-inclusion-is-full-Subgroup :
    is-full-Subgroup G H →
    is-iso-Group (group-Subgroup G H) G (hom-inclusion-Subgroup G H)
  is-iso-inclusion-is-full-Subgroup K =
    is-iso-is-equiv-hom-Group
      ( group-Subgroup G H)
      ( G)
      ( hom-inclusion-Subgroup G H)
      ( is-equiv-inclusion-is-full-subtype (subset-Subgroup G H) K)

  iso-inclusion-is-full-Subgroup :
    is-full-Subgroup G H → iso-Group (group-Subgroup G H) G
  pr1 (iso-inclusion-is-full-Subgroup K) = hom-inclusion-Subgroup G H
  pr2 (iso-inclusion-is-full-Subgroup K) = is-iso-inclusion-is-full-Subgroup K

  is-full-is-iso-inclusion-Subgroup :
    is-iso-Group (group-Subgroup G H) G (hom-inclusion-Subgroup G H) →
    is-full-Subgroup G H
  is-full-is-iso-inclusion-Subgroup K =
    is-full-is-equiv-inclusion-subtype
      ( subset-Subgroup G H)
      ( is-equiv-is-iso-Group
        ( group-Subgroup G H)
        ( G)
        ( hom-inclusion-Subgroup G H)
        ( K))
```
