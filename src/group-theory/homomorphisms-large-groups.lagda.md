# Homomorphisms of large groups

```agda
module group-theory.homomorphisms-large-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-large-semigroups
open import group-theory.large-groups
```

</details>

## Idea

A
{{#concept "homomorphism" Disambiguation="of large groups" Agda=hom-Large-Group}}
of [large groups](group-theory.large-groups.md) is a
[homomorphism](group-theory.homomorphisms-large-semigroups.md) of their
underlying [large semigroups](group-theory.large-semigroups.md).

## Definition

We create a single-field record to ensure that the source and target large
groups can be determined implicitly from the homomorphism.

```agda
record
  hom-Large-Group
    {α β : Level → Level}
    {γ δ : Level → Level → Level}
    (G : Large-Group α γ)
    (H : Large-Group β δ) :
    UUω
  where

  constructor
    make-hom-Large-Group

  field
    hom-large-semigroup-hom-Large-Group :
      hom-Large-Semigroup
        ( large-semigroup-Large-Group G)
        ( large-semigroup-Large-Group H)

  map-hom-Large-Group :
    {l : Level} → type-Large-Group G l → type-Large-Group H l
  map-hom-Large-Group =
    map-hom-Large-Semigroup hom-large-semigroup-hom-Large-Group

  preserves-mul-hom-Large-Group :
    {l1 l2 : Level} {x : type-Large-Group G l1} {y : type-Large-Group G l2} →
    map-hom-Large-Group (mul-Large-Group G x y) ＝
    mul-Large-Group H (map-hom-Large-Group x) (map-hom-Large-Group y)
  preserves-mul-hom-Large-Group =
    preserves-mul-hom-Large-Semigroup hom-large-semigroup-hom-Large-Group

open hom-Large-Group public
```

## Properties

### Small group homomorphisms from large group homomorphisms

```agda
module _
  {α β : Level → Level}
  {γ δ : Level → Level → Level}
  {G : Large-Group α γ}
  {H : Large-Group β δ}
  (f : hom-Large-Group G H)
  where

  hom-group-hom-Large-Group :
    (l : Level) → hom-Group (group-Large-Group G l) (group-Large-Group H l)
  hom-group-hom-Large-Group l =
    ( map-hom-Large-Group f ,
      preserves-mul-hom-Large-Group f)
```

### Large group homomorphisms preserve units

```agda
module _
  {α β : Level → Level}
  {γ δ : Level → Level → Level}
  {G : Large-Group α γ}
  {H : Large-Group β δ}
  (f : hom-Large-Group G H)
  where

  abstract
    preserves-raise-unit-hom-Large-Group :
      (l : Level) →
      map-hom-Large-Group f (raise-unit-Large-Group G l) ＝
      raise-unit-Large-Group H l
    preserves-raise-unit-hom-Large-Group l =
      preserves-unit-hom-Group
        ( group-Large-Group G l)
        ( group-Large-Group H l)
        ( hom-group-hom-Large-Group f l)
```
