# Isomorphisms of groups

```agda
module group-theory.isomorphisms-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-large-precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.category-of-semigroups
open import group-theory.equivalences-semigroups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-semigroups
open import group-theory.precategory-of-groups
```

</details>

## Definitions

### Group isomorphisms

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  is-iso-hom-Group : type-hom-Group G H → UU (l1 ⊔ l2)
  is-iso-hom-Group =
    is-iso-Large-Precategory Group-Large-Precategory {X = G} {Y = H}

  type-iso-Group : UU (l1 ⊔ l2)
  type-iso-Group = iso-Large-Precategory Group-Large-Precategory G H

  hom-iso-Group : type-iso-Group → type-hom-Group G H
  hom-iso-Group = hom-iso-Large-Precategory Group-Large-Precategory G H

  is-iso-hom-iso-Group :
    (f : type-iso-Group) → is-iso-hom-Group (hom-iso-Group f)
  is-iso-hom-iso-Group =
    is-iso-hom-iso-Large-Precategory Group-Large-Precategory G H

  hom-inv-iso-Group : type-iso-Group → type-hom-Group H G
  hom-inv-iso-Group = hom-inv-iso-Large-Precategory Group-Large-Precategory G H

  is-equiv-hom-Group : type-hom-Group G H → UU (l1 ⊔ l2)
  is-equiv-hom-Group =
    is-equiv-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  equiv-Group : UU (l1 ⊔ l2)
  equiv-Group = equiv-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-iso-is-equiv-hom-Group :
    (f : type-hom-Group G H) → is-equiv-hom-Group f → is-iso-hom-Group f
  is-iso-is-equiv-hom-Group =
    is-iso-is-equiv-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-equiv-is-iso-hom-Group :
    (f : type-hom-Group G H) → is-iso-hom-Group f → is-equiv-hom-Group f
  is-equiv-is-iso-hom-Group =
    is-equiv-is-iso-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  equiv-iso-equiv-Group : equiv-Group ≃ type-iso-Group
  equiv-iso-equiv-Group =
    equiv-iso-equiv-Semigroup (semigroup-Group G) (semigroup-Group H)

  iso-equiv-Group : equiv-Group → type-iso-Group
  iso-equiv-Group = map-equiv equiv-iso-equiv-Group
```

### The identity isomorphism

```agda
module _
  {l : Level} (G : Group l)
  where

  id-iso-Group : type-iso-Group G G
  id-iso-Group = id-iso-Large-Precategory Group-Large-Precategory {X = G}
```

## Properties

### The total space of group isomorphisms from a given group `G` is contractible

```agda
module _
  {l : Level} (G : Group l)
  where

  iso-eq-Group : (H : Group l) → Id G H → type-iso-Group G H
  iso-eq-Group = iso-eq-Large-Precategory Group-Large-Precategory G

  abstract
    extensionality-Group' : (H : Group l) → Id G H ≃ type-iso-Group G H
    extensionality-Group' H =
      ( extensionality-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)) ∘e
      ( equiv-ap-inclusion-subtype is-group-Prop {s = G} {t = H})

  abstract
    is-contr-total-iso-Group : is-contr (Σ (Group l) (type-iso-Group G))
    is-contr-total-iso-Group =
      is-contr-equiv'
        ( Σ (Group l) (Id G))
        ( equiv-tot extensionality-Group')
        ( is-contr-total-path G)
```

### Group isomorphisms are stable by composition

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3)
  where

  comp-iso-Group :
    type-iso-Group H K → type-iso-Group G H → type-iso-Group G K
  comp-iso-Group = comp-iso-Large-Precategory Group-Large-Precategory G H K
```

### Group isomorphisms are stable by inversion

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  inv-iso-Group : type-iso-Group G H → type-iso-Group H G
  inv-iso-Group = inv-iso-Large-Precategory Group-Large-Precategory G H
```
