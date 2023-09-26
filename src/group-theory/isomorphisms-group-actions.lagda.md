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
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  private
    C = Abstract-Group-Action-Large-Precategory G

  is-iso-Abstract-Group-Action :
    (f : hom-Abstract-Group-Action G X Y) → UU (l1 ⊔ l2 ⊔ l3)
  is-iso-Abstract-Group-Action =
    is-iso-Large-Precategory C {X = X} {Y = Y}

  type-iso-Abstract-Group-Action : UU (l1 ⊔ l2 ⊔ l3)
  type-iso-Abstract-Group-Action = iso-Large-Precategory C X Y

  hom-iso-Abstract-Group-Action :
    type-iso-Abstract-Group-Action → hom-Abstract-Group-Action G X Y
  hom-iso-Abstract-Group-Action = hom-iso-Large-Precategory C {X = X} {Y = Y}

  map-iso-Abstract-Group-Action :
    type-iso-Abstract-Group-Action →
    type-Abstract-Group-Action G X → type-Abstract-Group-Action G Y
  map-iso-Abstract-Group-Action f =
    map-hom-Abstract-Group-Action G X Y (hom-iso-Abstract-Group-Action f)

  coherence-square-iso-Abstract-Group-Action :
    (f : type-iso-Abstract-Group-Action) (g : type-Group G) →
    coherence-square-maps
      ( map-iso-Abstract-Group-Action f)
      ( mul-Abstract-Group-Action G X g)
      ( mul-Abstract-Group-Action G Y g)
      ( map-iso-Abstract-Group-Action f)
  coherence-square-iso-Abstract-Group-Action f =
    coherence-square-hom-Abstract-Group-Action G X Y
      ( hom-iso-Abstract-Group-Action f)

  hom-inv-iso-Abstract-Group-Action :
    type-iso-Abstract-Group-Action → hom-Abstract-Group-Action G Y X
  hom-inv-iso-Abstract-Group-Action =
    hom-inv-iso-Large-Precategory C {X = X} {Y = Y}

  map-hom-inv-iso-Abstract-Group-Action :
    type-iso-Abstract-Group-Action →
    type-Abstract-Group-Action G Y → type-Abstract-Group-Action G X
  map-hom-inv-iso-Abstract-Group-Action f =
    map-hom-Abstract-Group-Action G Y X
      ( hom-inv-iso-Abstract-Group-Action f)

  is-section-hom-inv-iso-Abstract-Group-Action :
    (f : type-iso-Abstract-Group-Action) →
    Id
      ( comp-hom-Abstract-Group-Action G Y X Y
        ( hom-iso-Abstract-Group-Action f)
        ( hom-inv-iso-Abstract-Group-Action f))
      ( id-hom-Abstract-Group-Action G Y)
  is-section-hom-inv-iso-Abstract-Group-Action =
    is-section-hom-inv-iso-Large-Precategory C {X = X} {Y = Y}

  is-retraction-hom-inv-iso-Abstract-Group-Action :
    (f : type-iso-Abstract-Group-Action) →
    Id
      ( comp-hom-Abstract-Group-Action G X Y X
        ( hom-inv-iso-Abstract-Group-Action f)
        ( hom-iso-Abstract-Group-Action f))
      ( id-hom-Abstract-Group-Action G X)
  is-retraction-hom-inv-iso-Abstract-Group-Action =
    is-retraction-hom-inv-iso-Large-Precategory C {X = X} {Y = Y}

  is-iso-iso-Abstract-Group-Action :
    (f : type-iso-Abstract-Group-Action) →
    is-iso-Abstract-Group-Action (hom-iso-Abstract-Group-Action f)
  is-iso-iso-Abstract-Group-Action =
    is-iso-iso-Large-Precategory C {X = X} {Y = Y}

  equiv-iso-Abstract-Group-Action :
    type-iso-Abstract-Group-Action → equiv-Abstract-Group-Action G X Y
  pr1 (pr1 (equiv-iso-Abstract-Group-Action f)) =
    map-iso-Abstract-Group-Action f
  pr2 (pr1 (equiv-iso-Abstract-Group-Action f)) =
    is-equiv-is-invertible
      ( map-hom-inv-iso-Abstract-Group-Action f)
      ( htpy-eq-hom-Abstract-Group-Action G Y Y
        ( comp-hom-Abstract-Group-Action G Y X Y
          ( hom-iso-Abstract-Group-Action f)
          ( hom-inv-iso-Abstract-Group-Action f))
        ( id-hom-Abstract-Group-Action G Y)
        ( is-section-hom-inv-iso-Abstract-Group-Action f))
      ( htpy-eq-hom-Abstract-Group-Action G X X
        ( comp-hom-Abstract-Group-Action G X Y X
          ( hom-inv-iso-Abstract-Group-Action f)
          ( hom-iso-Abstract-Group-Action f))
        ( id-hom-Abstract-Group-Action G X)
        ( is-retraction-hom-inv-iso-Abstract-Group-Action f))
  pr2 (equiv-iso-Abstract-Group-Action f) =
    coherence-square-iso-Abstract-Group-Action f
```
