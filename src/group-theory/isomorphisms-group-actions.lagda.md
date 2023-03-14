# Isomorphisms of group actions

```agda
module group-theory.isomorphisms-group-actions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-large-precategories

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
    C = Abstract-Group-Action-Large-Precat G

  is-iso-hom-Abstract-Group-Action :
    (f : type-hom-Abstract-Group-Action G X Y) → UU (l1 ⊔ l2 ⊔ l3)
  is-iso-hom-Abstract-Group-Action = is-iso-Large-Precat C {X = X} {Y = Y}

  type-iso-Abstract-Group-Action : UU (l1 ⊔ l2 ⊔ l3)
  type-iso-Abstract-Group-Action = iso-Large-Precat C X Y

  hom-iso-Abstract-Group-Action :
    type-iso-Abstract-Group-Action → type-hom-Abstract-Group-Action G X Y
  hom-iso-Abstract-Group-Action = hom-iso-Large-Precat C X Y

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
    type-iso-Abstract-Group-Action → type-hom-Abstract-Group-Action G Y X
  hom-inv-iso-Abstract-Group-Action = hom-inv-iso-Large-Precat C X Y

  map-hom-inv-iso-Abstract-Group-Action :
    type-iso-Abstract-Group-Action →
    type-Abstract-Group-Action G Y → type-Abstract-Group-Action G X
  map-hom-inv-iso-Abstract-Group-Action f =
    map-hom-Abstract-Group-Action G Y X
      ( hom-inv-iso-Abstract-Group-Action f)

  issec-hom-inv-iso-Abstract-Group-Action :
    (f : type-iso-Abstract-Group-Action) →
    Id ( comp-hom-Abstract-Group-Action G Y X Y
         ( hom-iso-Abstract-Group-Action f)
         ( hom-inv-iso-Abstract-Group-Action f))
       ( id-hom-Abstract-Group-Action G Y)
  issec-hom-inv-iso-Abstract-Group-Action =
    is-sec-hom-inv-iso-Large-Precat C X Y

  isretr-hom-inv-iso-Abstract-Group-Action :
    (f : type-iso-Abstract-Group-Action) →
    Id ( comp-hom-Abstract-Group-Action G X Y X
         ( hom-inv-iso-Abstract-Group-Action f)
         ( hom-iso-Abstract-Group-Action f))
       ( id-hom-Abstract-Group-Action G X)
  isretr-hom-inv-iso-Abstract-Group-Action = is-retr-hom-inv-iso-Large-Precat C X Y

  is-iso-hom-iso-Abstract-Group-Action :
    (f : type-iso-Abstract-Group-Action) →
    is-iso-hom-Abstract-Group-Action (hom-iso-Abstract-Group-Action f)
  is-iso-hom-iso-Abstract-Group-Action = is-iso-hom-iso-Large-Precat C X Y

  equiv-iso-Abstract-Group-Action :
    type-iso-Abstract-Group-Action → equiv-Abstract-Group-Action G X Y
  pr1 (pr1 (equiv-iso-Abstract-Group-Action f)) =
    map-iso-Abstract-Group-Action f
  pr2 (pr1 (equiv-iso-Abstract-Group-Action f)) =
    is-equiv-has-inverse
      ( map-hom-inv-iso-Abstract-Group-Action f)
      ( htpy-eq-hom-Abstract-Group-Action G Y Y
        ( comp-hom-Abstract-Group-Action G Y X Y
          ( hom-iso-Abstract-Group-Action f)
          ( hom-inv-iso-Abstract-Group-Action f))
        ( id-hom-Abstract-Group-Action G Y)
        ( issec-hom-inv-iso-Abstract-Group-Action f))
      ( htpy-eq-hom-Abstract-Group-Action G X X
        ( comp-hom-Abstract-Group-Action G X Y X
          ( hom-inv-iso-Abstract-Group-Action f)
          ( hom-iso-Abstract-Group-Action f))
        ( id-hom-Abstract-Group-Action G X)
        ( isretr-hom-inv-iso-Abstract-Group-Action f))
  pr2 (equiv-iso-Abstract-Group-Action f) =
    coherence-square-iso-Abstract-Group-Action f
```
