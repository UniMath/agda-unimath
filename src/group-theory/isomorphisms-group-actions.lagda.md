# Isomorphisms of group actions

```agda
module group-theory.isomorphisms-group-actions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.equivalences-group-actions
open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-group-actions
open import group-theory.precategory-of-group-actions
```

</details>

## Definition

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (X : action-Group G l2)
  (Y : action-Group G l3)
  where

  private
    C = action-Group-Large-Precategory G

  is-iso-action-Group :
    (f : hom-action-Group G X Y) → UU (l1 ⊔ l2 ⊔ l3)
  is-iso-action-Group =
    is-iso-Large-Precategory C {X = X} {Y = Y}

  iso-action-Group : UU (l1 ⊔ l2 ⊔ l3)
  iso-action-Group = iso-Large-Precategory C X Y

  hom-iso-action-Group :
    iso-action-Group → hom-action-Group G X Y
  hom-iso-action-Group = hom-iso-Large-Precategory C {X = X} {Y = Y}

  map-iso-action-Group :
    iso-action-Group →
    type-action-Group G X → type-action-Group G Y
  map-iso-action-Group f =
    map-hom-action-Group G X Y (hom-iso-action-Group f)

  preserves-action-iso-action-Group :
    (f : iso-action-Group) (g : type-Group G) →
    coherence-square-maps
      ( map-iso-action-Group f)
      ( mul-action-Group G X g)
      ( mul-action-Group G Y g)
      ( map-iso-action-Group f)
  preserves-action-iso-action-Group f =
    preserves-action-hom-action-Group G X Y
      ( hom-iso-action-Group f)

  hom-inv-iso-action-Group :
    iso-action-Group → hom-action-Group G Y X
  hom-inv-iso-action-Group =
    hom-inv-iso-Large-Precategory C {X = X} {Y = Y}

  map-hom-inv-iso-action-Group :
    iso-action-Group →
    type-action-Group G Y → type-action-Group G X
  map-hom-inv-iso-action-Group f =
    map-hom-action-Group G Y X
      ( hom-inv-iso-action-Group f)

  is-section-hom-inv-iso-action-Group :
    (f : iso-action-Group) →
    Id
      ( comp-hom-action-Group G Y X Y
        ( hom-iso-action-Group f)
        ( hom-inv-iso-action-Group f))
      ( id-hom-action-Group G Y)
  is-section-hom-inv-iso-action-Group =
    is-section-hom-inv-iso-Large-Precategory C {X = X} {Y = Y}

  is-retraction-hom-inv-iso-action-Group :
    (f : iso-action-Group) →
    Id
      ( comp-hom-action-Group G X Y X
        ( hom-inv-iso-action-Group f)
        ( hom-iso-action-Group f))
      ( id-hom-action-Group G X)
  is-retraction-hom-inv-iso-action-Group =
    is-retraction-hom-inv-iso-Large-Precategory C {X = X} {Y = Y}

  is-iso-iso-action-Group :
    (f : iso-action-Group) →
    is-iso-action-Group (hom-iso-action-Group f)
  is-iso-iso-action-Group =
    is-iso-iso-Large-Precategory C {X = X} {Y = Y}

  equiv-iso-action-Group :
    iso-action-Group → equiv-action-Group G X Y
  pr1 (pr1 (equiv-iso-action-Group f)) =
    map-iso-action-Group f
  pr2 (pr1 (equiv-iso-action-Group f)) =
    is-equiv-is-invertible
      ( map-hom-inv-iso-action-Group f)
      ( htpy-eq-hom-action-Group G Y Y
        ( comp-hom-action-Group G Y X Y
          ( hom-iso-action-Group f)
          ( hom-inv-iso-action-Group f))
        ( id-hom-action-Group G Y)
        ( is-section-hom-inv-iso-action-Group f))
      ( htpy-eq-hom-action-Group G X X
        ( comp-hom-action-Group G X Y X
          ( hom-inv-iso-action-Group f)
          ( hom-iso-action-Group f))
        ( id-hom-action-Group G X)
        ( is-retraction-hom-inv-iso-action-Group f))
  pr2 (equiv-iso-action-Group f) =
    preserves-action-iso-action-Group f
```
