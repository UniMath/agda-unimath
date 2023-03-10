# The full subgroup of a group

```agda
module group-theory.full-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.function-extensionality
open import foundation.functions
open import foundation.identity-types
open import foundation.powersets
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-groups
open import group-theory.subgroups
```

</details>

## Idea

The full subset of a group is a normal subgroup.

## Definition

### Full subgroups

```agda
is-full-Subgroup :
  {l1 l2 : Level} (G : Group l1) → Subgroup l2 G → UU (l1 ⊔ l2)
is-full-Subgroup G H = is-full-subtype (subset-Subgroup G H)
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

is-closed-under-mul-full-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  is-closed-under-mul-subset-Group G (subset-full-Subgroup l2 G)
is-closed-under-mul-full-Subgroup G x y _ _ =
  is-in-full-subtype (mul-Group G x y)

is-closed-under-inv-full-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  is-closed-under-inv-subset-Group G (subset-full-Subgroup l2 G)
is-closed-under-inv-full-Subgroup G x _ =
  is-in-full-subtype (inv-Group G x)

full-Subgroup : {l1 : Level} (l2 : Level) (G : Group l1) → Subgroup l2 G
pr1 (full-Subgroup l2 G) = subset-full-Subgroup l2 G
pr1 (pr2 (full-Subgroup l2 G)) = contains-unit-full-Subgroup G
pr1 (pr2 (pr2 (full-Subgroup l2 G))) = is-closed-under-mul-full-Subgroup G
pr2 (pr2 (pr2 (full-Subgroup l2 G))) = is-closed-under-inv-full-Subgroup G

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

  inclusion-group-full-Subgroup : type-hom-Group group-full-Subgroup G
  inclusion-group-full-Subgroup =
    inclusion-group-Subgroup G (full-Subgroup l2 G)

  preserves-mul-inclusion-group-full-Subgroup :
    preserves-mul-Group group-full-Subgroup G inclusion-full-Subgroup
  preserves-mul-inclusion-group-full-Subgroup =
    preserves-mul-inclusion-group-Subgroup G (full-Subgroup l2 G)

  equiv-inclusion-group-full-Subgroup : equiv-Group group-full-Subgroup G
  pr1 equiv-inclusion-group-full-Subgroup = equiv-inclusion-full-Subgroup
  pr2 equiv-inclusion-group-full-Subgroup =
    preserves-mul-inclusion-group-full-Subgroup

  iso-full-Subgroup : type-iso-Group group-full-Subgroup G
  iso-full-Subgroup =
    iso-equiv-Group group-full-Subgroup G equiv-inclusion-group-full-Subgroup

  inv-iso-full-Subgroup :
    type-iso-Group G group-full-Subgroup
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
    is-iso-hom-Group (group-Subgroup G H) G (inclusion-group-Subgroup G H)
  is-iso-inclusion-is-full-Subgroup K =
    is-iso-is-equiv-hom-Group
      ( group-Subgroup G H)
      ( G)
      ( inclusion-group-Subgroup G H)
      ( is-equiv-inclusion-is-full-subtype (subset-Subgroup G H) K)

  iso-inclusion-is-full-Subgroup :
    is-full-Subgroup G H → type-iso-Group (group-Subgroup G H) G
  pr1 (iso-inclusion-is-full-Subgroup K) = inclusion-group-Subgroup G H
  pr2 (iso-inclusion-is-full-Subgroup K) = is-iso-inclusion-is-full-Subgroup K

  is-full-is-iso-inclusion-Subgroup :
    is-iso-hom-Group (group-Subgroup G H) G (inclusion-group-Subgroup G H) →
    is-full-Subgroup G H
  is-full-is-iso-inclusion-Subgroup K =
    is-full-is-equiv-inclusion-subtype
      ( subset-Subgroup G H)
      ( is-equiv-is-iso-hom-Group
        ( group-Subgroup G H)
        ( G)
        ( inclusion-group-Subgroup G H)
        ( K))
```
