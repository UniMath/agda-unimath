# Equivalences of group actions

```agda
module group-theory.equivalences-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-group-actions
open import group-theory.homomorphisms-groups
open import group-theory.symmetric-groups
```

</details>

## Idea

A morphism of G-sets is said to be an equivalence if its underlying map is an
equivalence.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  is-equiv-hom-Abstract-Group-Action :
    type-hom-Abstract-Group-Action G X Y → UU (l2 ⊔ l3)
  is-equiv-hom-Abstract-Group-Action f =
    is-equiv (map-hom-Abstract-Group-Action G X Y f)

  equiv-Abstract-Group-Action : UU (l1 ⊔ l2 ⊔ l3)
  equiv-Abstract-Group-Action =
    Σ ( type-Abstract-Group-Action G X ≃ type-Abstract-Group-Action G Y)
      ( λ e →
        ( g : type-Group G) →
        coherence-square-maps
          ( map-equiv e)
          ( mul-Abstract-Group-Action G X g)
          ( mul-Abstract-Group-Action G Y g)
          ( map-equiv e))

  equiv-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action →
    type-Abstract-Group-Action G X ≃ type-Abstract-Group-Action G Y
  equiv-equiv-Abstract-Group-Action = pr1

  map-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action →
    type-Abstract-Group-Action G X → type-Abstract-Group-Action G Y
  map-equiv-Abstract-Group-Action e =
    map-equiv (equiv-equiv-Abstract-Group-Action e)

  is-equiv-map-equiv-Abstract-Group-Action :
    (e : equiv-Abstract-Group-Action) →
    is-equiv (map-equiv-Abstract-Group-Action e)
  is-equiv-map-equiv-Abstract-Group-Action e =
    is-equiv-map-equiv (equiv-equiv-Abstract-Group-Action e)

  coherence-square-equiv-Abstract-Group-Action :
    (e : equiv-Abstract-Group-Action) (g : type-Group G) →
    coherence-square-maps
      ( map-equiv-Abstract-Group-Action e)
      ( mul-Abstract-Group-Action G X g)
      ( mul-Abstract-Group-Action G Y g)
      ( map-equiv-Abstract-Group-Action e)
  coherence-square-equiv-Abstract-Group-Action = pr2

  hom-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action → type-hom-Abstract-Group-Action G X Y
  pr1 (hom-equiv-Abstract-Group-Action e) =
    map-equiv-Abstract-Group-Action e
  pr2 (hom-equiv-Abstract-Group-Action e) =
    coherence-square-equiv-Abstract-Group-Action e

  is-equiv-hom-equiv-Abstract-Group-Action :
    (e : equiv-Abstract-Group-Action) →
    is-equiv-hom-Abstract-Group-Action (hom-equiv-Abstract-Group-Action e)
  is-equiv-hom-equiv-Abstract-Group-Action =
    is-equiv-map-equiv-Abstract-Group-Action
```

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3) (e : equiv-Abstract-Group-Action G X Y)
  where

  htpy-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) → UU (l2 ⊔ l3)
  htpy-equiv-Abstract-Group-Action f =
    htpy-hom-Abstract-Group-Action G X Y
      ( hom-equiv-Abstract-Group-Action G X Y e)
      ( hom-equiv-Abstract-Group-Action G X Y f)

  refl-htpy-equiv-Abstract-Group-Action : htpy-equiv-Abstract-Group-Action e
  refl-htpy-equiv-Abstract-Group-Action =
    refl-htpy-hom-Abstract-Group-Action G X Y
      ( hom-equiv-Abstract-Group-Action G X Y e)

  htpy-eq-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id e f → htpy-equiv-Abstract-Group-Action f
  htpy-eq-equiv-Abstract-Group-Action .e refl =
    refl-htpy-equiv-Abstract-Group-Action

  is-contr-total-htpy-equiv-Abstract-Group-Action :
    is-contr
      ( Σ ( equiv-Abstract-Group-Action G X Y)
          ( htpy-equiv-Abstract-Group-Action))
  is-contr-total-htpy-equiv-Abstract-Group-Action =
    is-contr-equiv
      ( Σ ( Σ ( type-hom-Abstract-Group-Action G X Y) (λ f → is-equiv (pr1 f)))
          ( λ f →
            htpy-hom-Abstract-Group-Action G X Y
              ( hom-equiv-Abstract-Group-Action G X Y e)
              ( pr1 f)))
      ( equiv-Σ
        ( λ f →
          htpy-hom-Abstract-Group-Action G X Y
            ( hom-equiv-Abstract-Group-Action G X Y e)
            ( pr1 f))
        ( equiv-right-swap-Σ)
        ( λ { (pair (pair f E) H) → id-equiv}))
      ( is-contr-total-Eq-subtype
        ( is-contr-total-htpy-hom-Abstract-Group-Action G X Y
          ( hom-equiv-Abstract-Group-Action G X Y e))
        ( λ f → is-property-is-equiv (pr1 f))
        ( hom-equiv-Abstract-Group-Action G X Y e)
        ( refl-htpy)
        ( is-equiv-map-equiv (pr1 e)))

  is-equiv-htpy-eq-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    is-equiv (htpy-eq-equiv-Abstract-Group-Action f)
  is-equiv-htpy-eq-equiv-Abstract-Group-Action =
    fundamental-theorem-id
      is-contr-total-htpy-equiv-Abstract-Group-Action
      htpy-eq-equiv-Abstract-Group-Action

  extensionality-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id e f ≃ htpy-equiv-Abstract-Group-Action f
  pr1 (extensionality-equiv-Abstract-Group-Action f) =
    htpy-eq-equiv-Abstract-Group-Action f
  pr2 (extensionality-equiv-Abstract-Group-Action f) =
    is-equiv-htpy-eq-equiv-Abstract-Group-Action f

  eq-htpy-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    htpy-equiv-Abstract-Group-Action f → Id e f
  eq-htpy-equiv-Abstract-Group-Action f =
    map-inv-is-equiv (is-equiv-htpy-eq-equiv-Abstract-Group-Action f)

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  inv-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action G X Y → equiv-Abstract-Group-Action G Y X
  pr1 (inv-equiv-Abstract-Group-Action (pair e H)) = inv-equiv e
  pr2 (inv-equiv-Abstract-Group-Action (pair e H)) g =
    coherence-square-inv-horizontal
      ( e)
      ( mul-Abstract-Group-Action G X g)
      ( mul-Abstract-Group-Action G Y g)
      ( e)
      ( H g)

module _
  {l1 l2 l3 l4 : Level} (G : Group l1)
  (X : Abstract-Group-Action G l2) (Y : Abstract-Group-Action G l3)
  (Z : Abstract-Group-Action G l4)
  where

  comp-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action G Y Z → equiv-Abstract-Group-Action G X Y →
    equiv-Abstract-Group-Action G X Z
  pr1 (comp-equiv-Abstract-Group-Action (pair f K) (pair e H)) = f ∘e e
  pr2 (comp-equiv-Abstract-Group-Action (pair f K) (pair e H)) g =
    pasting-horizontal-coherence-square-maps
      ( map-equiv e)
      ( map-equiv f)
      ( mul-Abstract-Group-Action G X g)
      ( mul-Abstract-Group-Action G Y g)
      ( mul-Abstract-Group-Action G Z g)
      ( map-equiv e)
      ( map-equiv f)
      ( H g)
      ( K g)

module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  id-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action G X X
  pr1 id-equiv-Abstract-Group-Action = id-equiv
  pr2 id-equiv-Abstract-Group-Action g = refl-htpy

  equiv-eq-Abstract-Group-Action :
    (Y : Abstract-Group-Action G l2) →
    Id X Y → equiv-Abstract-Group-Action G X Y
  equiv-eq-Abstract-Group-Action .X refl = id-equiv-Abstract-Group-Action

  abstract
    is-contr-total-equiv-Abstract-Group-Action :
      is-contr
        ( Σ ( Abstract-Group-Action G l2)
            ( equiv-Abstract-Group-Action G X))
    is-contr-total-equiv-Abstract-Group-Action =
      is-contr-total-Eq-structure
        ( λ Y ν e →
          (g : type-Group G) →
          htpy-equiv
            ( e ∘e map-hom-Group G (symmetric-Group (pr1 X)) (pr2 X) g)
            ( map-hom-Group G (symmetric-Group Y) ν g ∘e e))
        ( is-contr-total-equiv-Set (pr1 X))
        ( pair (pr1 X) id-equiv)
        ( is-contr-equiv
          ( Σ ( type-hom-Group G (symmetric-Group (pr1 X)))
              ( htpy-hom-Group G (symmetric-Group (pr1 X)) (pr2 X)))
          ( equiv-tot
            ( λ f →
              equiv-map-Π
                ( λ g →
                  inv-equiv
                    ( extensionality-equiv
                      ( map-hom-Group G (symmetric-Group (pr1 X)) (pr2 X) g)
                      ( map-hom-Group G (symmetric-Group (pr1 X)) f g)))))
          ( is-contr-total-htpy-hom-Group G
            ( symmetric-Group (pr1 X))
            ( pr2 X)))

  abstract
    is-equiv-equiv-eq-Abstract-Group-Action :
      (Y : Abstract-Group-Action G l2) →
      is-equiv (equiv-eq-Abstract-Group-Action Y)
    is-equiv-equiv-eq-Abstract-Group-Action =
      fundamental-theorem-id
        is-contr-total-equiv-Abstract-Group-Action
        equiv-eq-Abstract-Group-Action

  eq-equiv-Abstract-Group-Action :
    (Y : Abstract-Group-Action G l2) →
    equiv-Abstract-Group-Action G X Y → Id X Y
  eq-equiv-Abstract-Group-Action Y =
    map-inv-is-equiv (is-equiv-equiv-eq-Abstract-Group-Action Y)

  extensionality-Abstract-Group-Action :
    (Y : Abstract-Group-Action G l2) →
    Id X Y ≃ equiv-Abstract-Group-Action G X Y
  pr1 (extensionality-Abstract-Group-Action Y) =
    equiv-eq-Abstract-Group-Action Y
  pr2 (extensionality-Abstract-Group-Action Y) =
    is-equiv-equiv-eq-Abstract-Group-Action Y

module _
  {l1 l2 l3 l4 l5 : Level} (G : Group l1) (X1 : Abstract-Group-Action G l2)
  (X2 : Abstract-Group-Action G l3) (X3 : Abstract-Group-Action G l4)
  (X4 : Abstract-Group-Action G l5)
  where

  associative-comp-equiv-Abstract-Group-Action :
    (h : equiv-Abstract-Group-Action G X3 X4)
    (g : equiv-Abstract-Group-Action G X2 X3)
    (f : equiv-Abstract-Group-Action G X1 X2) →
    Id
      ( comp-equiv-Abstract-Group-Action G X1 X2 X4
        ( comp-equiv-Abstract-Group-Action G X2 X3 X4 h g)
        ( f))
      ( comp-equiv-Abstract-Group-Action G X1 X3 X4 h
        ( comp-equiv-Abstract-Group-Action G X1 X2 X3 g f))
  associative-comp-equiv-Abstract-Group-Action h g f =
    eq-htpy-equiv-Abstract-Group-Action G X1 X4
      ( comp-equiv-Abstract-Group-Action G X1 X2 X4
        ( comp-equiv-Abstract-Group-Action G X2 X3 X4 h g)
        ( f))
      ( comp-equiv-Abstract-Group-Action G X1 X3 X4 h
        ( comp-equiv-Abstract-Group-Action G X1 X2 X3 g f))
      ( refl-htpy)

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  left-unit-law-comp-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id
      ( comp-equiv-Abstract-Group-Action G X Y Y
        ( id-equiv-Abstract-Group-Action G Y)
        ( f))
      ( f)
  left-unit-law-comp-equiv-Abstract-Group-Action f =
    eq-htpy-equiv-Abstract-Group-Action G X Y
      ( comp-equiv-Abstract-Group-Action G X Y Y
        ( id-equiv-Abstract-Group-Action G Y)
        ( f))
      ( f)
      ( refl-htpy)

  right-unit-law-comp-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id
      ( comp-equiv-Abstract-Group-Action G X X Y f
        ( id-equiv-Abstract-Group-Action G X))
      ( f)
  right-unit-law-comp-equiv-Abstract-Group-Action f =
    eq-htpy-equiv-Abstract-Group-Action G X Y
      ( comp-equiv-Abstract-Group-Action G X X Y f
        ( id-equiv-Abstract-Group-Action G X))
      ( f)
      ( refl-htpy)

  left-inverse-law-comp-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id
      ( comp-equiv-Abstract-Group-Action G X Y X
        ( inv-equiv-Abstract-Group-Action G X Y f)
        ( f))
      ( id-equiv-Abstract-Group-Action G X)
  left-inverse-law-comp-equiv-Abstract-Group-Action f =
    eq-htpy-equiv-Abstract-Group-Action G X X
      ( comp-equiv-Abstract-Group-Action G X Y X
        ( inv-equiv-Abstract-Group-Action G X Y f)
        ( f))
      ( id-equiv-Abstract-Group-Action G X)
      ( is-retraction-map-inv-equiv (pr1 f))

  right-inverse-law-comp-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id
      ( comp-equiv-Abstract-Group-Action G Y X Y f
        ( inv-equiv-Abstract-Group-Action G X Y f))
      ( id-equiv-Abstract-Group-Action G Y)
  right-inverse-law-comp-equiv-Abstract-Group-Action f =
    eq-htpy-equiv-Abstract-Group-Action G Y Y
      ( comp-equiv-Abstract-Group-Action G Y X Y f
        ( inv-equiv-Abstract-Group-Action G X Y f))
      ( id-equiv-Abstract-Group-Action G Y)
      ( is-section-map-inv-equiv (pr1 f))
```
