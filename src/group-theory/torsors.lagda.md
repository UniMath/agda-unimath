# Torsors of abstract groups

```agda
module group-theory.torsors where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.transport
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.equivalences-group-actions
open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-groups
open import group-theory.mere-equivalences-group-actions
open import group-theory.principal-group-actions
open import group-theory.symmetric-groups

open import higher-group-theory.higher-groups
```

</details>

## Idea

A torsor of `G` is a group action wich merely equivalent to the principal group
action of `G`.

## Definitions

### Torsors

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  is-torsor-Abstract-Group-Prop : Prop (l1 ⊔ l2)
  is-torsor-Abstract-Group-Prop =
    mere-equiv-Abstract-Group-Action-Prop G
      ( principal-Abstract-Group-Action G)
      ( X)

  is-torsor-Abstract-Group : UU (l1 ⊔ l2)
  is-torsor-Abstract-Group = type-Prop is-torsor-Abstract-Group-Prop

  is-prop-is-torsor-Abstract-Group : is-prop is-torsor-Abstract-Group
  is-prop-is-torsor-Abstract-Group =
    is-prop-type-Prop is-torsor-Abstract-Group-Prop

module _
  {l1 : Level} (G : Group l1)
  where

  Torsor-Abstract-Group : (l : Level) → UU (l1 ⊔ lsuc l)
  Torsor-Abstract-Group l =
    Σ ( Abstract-Group-Action G l)
      ( is-torsor-Abstract-Group G)

  action-Torsor-Abstract-Group :
    {l : Level} → Torsor-Abstract-Group l → Abstract-Group-Action G l
  action-Torsor-Abstract-Group = pr1

  set-Torsor-Abstract-Group :
    {l : Level} → Torsor-Abstract-Group l → Set l
  set-Torsor-Abstract-Group X =
    set-Abstract-Group-Action G (action-Torsor-Abstract-Group X)

  type-Torsor-Abstract-Group :
    {l : Level} → Torsor-Abstract-Group l → UU l
  type-Torsor-Abstract-Group X =
    type-Set (set-Torsor-Abstract-Group X)

  is-set-type-Torsor-Abstract-Group :
    {l : Level} (X : Torsor-Abstract-Group l) →
    is-set (type-Torsor-Abstract-Group X)
  is-set-type-Torsor-Abstract-Group X =
    is-set-type-Set (set-Torsor-Abstract-Group X)

  mul-hom-Torsor-Abstract-Group :
    {l : Level} (X : Torsor-Abstract-Group l) →
    type-hom-Group G (symmetric-Group (set-Torsor-Abstract-Group X))
  mul-hom-Torsor-Abstract-Group X = pr2 (action-Torsor-Abstract-Group X)

  equiv-mul-Torsor-Abstract-Group :
    {l : Level} (X : Torsor-Abstract-Group l) → type-Group G →
    (type-Torsor-Abstract-Group X ≃ type-Torsor-Abstract-Group X)
  equiv-mul-Torsor-Abstract-Group X =
    equiv-mul-Abstract-Group-Action G (action-Torsor-Abstract-Group X)

  mul-Torsor-Abstract-Group :
    {l : Level} (X : Torsor-Abstract-Group l) →
    type-Group G → type-Torsor-Abstract-Group X → type-Torsor-Abstract-Group X
  mul-Torsor-Abstract-Group X =
    mul-Abstract-Group-Action G (action-Torsor-Abstract-Group X)

  is-torsor-action-Torsor-Abstract-Group :
    {l : Level} (X : Torsor-Abstract-Group l) →
    is-torsor-Abstract-Group G (action-Torsor-Abstract-Group X)
  is-torsor-action-Torsor-Abstract-Group = pr2
```

### Principal torsor

```agda
  principal-Torsor-Abstract-Group : Torsor-Abstract-Group l1
  pr1 principal-Torsor-Abstract-Group = principal-Abstract-Group-Action G
  pr2 principal-Torsor-Abstract-Group =
    unit-trunc-Prop
      ( id-equiv-Abstract-Group-Action G (principal-Abstract-Group-Action G))
```

## Properties

### Characterization of the identity type of `Torsor-Abstract-Group`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : Torsor-Abstract-Group G l2)
  where

  equiv-Torsor-Abstract-Group :
    {l3 : Level} (Y : Torsor-Abstract-Group G l3) → UU (l1 ⊔ l2 ⊔ l3)
  equiv-Torsor-Abstract-Group Y =
    equiv-Abstract-Group-Action G
      ( action-Torsor-Abstract-Group G X)
      ( action-Torsor-Abstract-Group G Y)

  id-equiv-Torsor-Abstract-Group : equiv-Torsor-Abstract-Group X
  id-equiv-Torsor-Abstract-Group =
    id-equiv-Abstract-Group-Action G (action-Torsor-Abstract-Group G X)

  equiv-eq-Torsor-Abstract-Group :
    (Y : Torsor-Abstract-Group G l2) → Id X Y → equiv-Torsor-Abstract-Group Y
  equiv-eq-Torsor-Abstract-Group .X refl =
    id-equiv-Torsor-Abstract-Group

  is-contr-total-equiv-Torsor-Abstract-Group :
    is-contr (Σ (Torsor-Abstract-Group G l2) (equiv-Torsor-Abstract-Group))
  is-contr-total-equiv-Torsor-Abstract-Group =
    is-contr-total-Eq-subtype
      ( is-contr-total-equiv-Abstract-Group-Action G
        ( action-Torsor-Abstract-Group G X))
      ( is-prop-is-torsor-Abstract-Group G)
      ( action-Torsor-Abstract-Group G X)
      ( id-equiv-Torsor-Abstract-Group)
      ( is-torsor-action-Torsor-Abstract-Group G X)

  is-equiv-equiv-eq-Torsor-Abstract-Group :
    (Y : Torsor-Abstract-Group G l2) →
    is-equiv (equiv-eq-Torsor-Abstract-Group Y)
  is-equiv-equiv-eq-Torsor-Abstract-Group =
    fundamental-theorem-id
      is-contr-total-equiv-Torsor-Abstract-Group
      equiv-eq-Torsor-Abstract-Group

  eq-equiv-Torsor-Abstract-Group :
    (Y : Torsor-Abstract-Group G l2) → equiv-Torsor-Abstract-Group Y → Id X Y
  eq-equiv-Torsor-Abstract-Group Y =
    map-inv-is-equiv (is-equiv-equiv-eq-Torsor-Abstract-Group Y)

  extensionality-Torsor-Abstract-Group :
    (Y : Torsor-Abstract-Group G l2) → Id X Y ≃ equiv-Torsor-Abstract-Group Y
  pr1 (extensionality-Torsor-Abstract-Group Y) =
    equiv-eq-Torsor-Abstract-Group Y
  pr2 (extensionality-Torsor-Abstract-Group Y) =
    is-equiv-equiv-eq-Torsor-Abstract-Group Y
```

### Characterization of the identity type of equivalences between `Torsor-Abstract-Group`

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Torsor-Abstract-Group G l2)
  (Y : Torsor-Abstract-Group G l3) (e : equiv-Torsor-Abstract-Group G X Y)
  where

  htpy-equiv-Torsor-Abstract-Group :
    equiv-Torsor-Abstract-Group G X Y → UU (l2 ⊔ l3)
  htpy-equiv-Torsor-Abstract-Group =
    htpy-equiv-Abstract-Group-Action G
      ( action-Torsor-Abstract-Group G X)
      ( action-Torsor-Abstract-Group G Y)
      ( e)

  refl-htpy-equiv-Torsor-Abstract-Group : htpy-equiv-Torsor-Abstract-Group e
  refl-htpy-equiv-Torsor-Abstract-Group =
    refl-htpy-equiv-Abstract-Group-Action G
      ( action-Torsor-Abstract-Group G X)
      ( action-Torsor-Abstract-Group G Y)
      ( e)

  htpy-eq-equiv-Torsor-Abstract-Group :
    (f : equiv-Torsor-Abstract-Group G X Y) →
    Id e f → htpy-equiv-Torsor-Abstract-Group f
  htpy-eq-equiv-Torsor-Abstract-Group .e refl =
    refl-htpy-equiv-Torsor-Abstract-Group

  is-contr-total-htpy-equiv-Torsor-Abstract-Group :
    is-contr
      ( Σ ( equiv-Torsor-Abstract-Group G X Y)
          ( htpy-equiv-Torsor-Abstract-Group))
  is-contr-total-htpy-equiv-Torsor-Abstract-Group =
    is-contr-total-htpy-equiv-Abstract-Group-Action G
      ( action-Torsor-Abstract-Group G X)
      ( action-Torsor-Abstract-Group G Y)
      ( e)

  is-equiv-htpy-eq-equiv-Torsor-Abstract-Group :
    (f : equiv-Torsor-Abstract-Group G X Y) →
    is-equiv (htpy-eq-equiv-Torsor-Abstract-Group f)
  is-equiv-htpy-eq-equiv-Torsor-Abstract-Group =
    fundamental-theorem-id
      is-contr-total-htpy-equiv-Torsor-Abstract-Group
      htpy-eq-equiv-Torsor-Abstract-Group

  extensionality-equiv-Torsor-Abstract-Group :
    (f : equiv-Torsor-Abstract-Group G X Y) →
    Id e f ≃ htpy-equiv-Torsor-Abstract-Group f
  pr1 (extensionality-equiv-Torsor-Abstract-Group f) =
    htpy-eq-equiv-Torsor-Abstract-Group f
  pr2 (extensionality-equiv-Torsor-Abstract-Group f) =
    is-equiv-htpy-eq-equiv-Torsor-Abstract-Group f

  eq-htpy-equiv-Torsor-Abstract-Group :
    (f : equiv-Torsor-Abstract-Group G X Y) →
    htpy-equiv-Torsor-Abstract-Group f → Id e f
  eq-htpy-equiv-Torsor-Abstract-Group f =
    map-inv-is-equiv (is-equiv-htpy-eq-equiv-Torsor-Abstract-Group f)
```

### Definition of the Group `aut-principal-Torsor-Abstract-Group` from a `Torsor-Abstract-Group`

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Torsor-Abstract-Group G l2)
  (Y : Torsor-Abstract-Group G l3)
  where

  is-set-equiv-Torsor-Abstract-Group :
    is-set (equiv-Torsor-Abstract-Group G X Y)
  is-set-equiv-Torsor-Abstract-Group e f =
    is-prop-equiv
      ( extensionality-equiv-Torsor-Abstract-Group G X Y e f)
      ( is-prop-Π
        ( λ x →
          is-set-type-Torsor-Abstract-Group G Y
            ( map-equiv (pr1 e) x)
            ( map-equiv (pr1 f) x)))

module _
  {l1 l2 l3 l4 : Level} (G : Group l1)
  (X : Torsor-Abstract-Group G l2) (Y : Torsor-Abstract-Group G l3)
  (Z : Torsor-Abstract-Group G l4)
  where

  comp-equiv-Torsor-Abstract-Group :
    equiv-Torsor-Abstract-Group G Y Z → equiv-Torsor-Abstract-Group G X Y →
    equiv-Torsor-Abstract-Group G X Z
  comp-equiv-Torsor-Abstract-Group =
    comp-equiv-Abstract-Group-Action G
      ( action-Torsor-Abstract-Group G X)
      ( action-Torsor-Abstract-Group G Y)
      ( action-Torsor-Abstract-Group G Z)

  comp-equiv-Torsor-Abstract-Group' :
    equiv-Torsor-Abstract-Group G X Y → equiv-Torsor-Abstract-Group G Y Z →
    equiv-Torsor-Abstract-Group G X Z
  comp-equiv-Torsor-Abstract-Group' e f =
    comp-equiv-Torsor-Abstract-Group f e

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Torsor-Abstract-Group G l2) (Y : Torsor-Abstract-Group G l3)
  where

  inv-equiv-Torsor-Abstract-Group :
    equiv-Torsor-Abstract-Group G X Y → equiv-Torsor-Abstract-Group G Y X
  inv-equiv-Torsor-Abstract-Group =
    inv-equiv-Abstract-Group-Action G
      ( action-Torsor-Abstract-Group G X)
      ( action-Torsor-Abstract-Group G Y)

module _
  {l1 l2 l3 l4 l5 : Level} (G : Group l1) (X1 : Torsor-Abstract-Group G l2)
  (X2 : Torsor-Abstract-Group G l3) (X3 : Torsor-Abstract-Group G l4)
  (X4 : Torsor-Abstract-Group G l5)
  where

  associative-comp-equiv-Torsor-Abstract-Group :
    (h : equiv-Torsor-Abstract-Group G X3 X4)
    (g : equiv-Torsor-Abstract-Group G X2 X3)
    (f : equiv-Torsor-Abstract-Group G X1 X2) →
    Id
      ( comp-equiv-Torsor-Abstract-Group G X1 X2 X4
        ( comp-equiv-Torsor-Abstract-Group G X2 X3 X4 h g)
        ( f))
      ( comp-equiv-Torsor-Abstract-Group G X1 X3 X4 h
        ( comp-equiv-Torsor-Abstract-Group G X1 X2 X3 g f))
  associative-comp-equiv-Torsor-Abstract-Group h g f =
    eq-htpy-equiv-Torsor-Abstract-Group G X1 X4
      ( comp-equiv-Torsor-Abstract-Group G X1 X2 X4
        ( comp-equiv-Torsor-Abstract-Group G X2 X3 X4 h g)
        ( f))
      ( comp-equiv-Torsor-Abstract-Group G X1 X3 X4 h
        ( comp-equiv-Torsor-Abstract-Group G X1 X2 X3 g f))
      ( refl-htpy)

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Torsor-Abstract-Group G l2)
  (Y : Torsor-Abstract-Group G l3)
  where

  left-unit-law-comp-equiv-Torsor-Abstract-Group :
    (f : equiv-Torsor-Abstract-Group G X Y) →
    Id
      ( comp-equiv-Torsor-Abstract-Group G X Y Y
        ( id-equiv-Torsor-Abstract-Group G Y)
        ( f))
      ( f)
  left-unit-law-comp-equiv-Torsor-Abstract-Group f =
    eq-htpy-equiv-Torsor-Abstract-Group G X Y
      ( comp-equiv-Torsor-Abstract-Group G X Y Y
        ( id-equiv-Torsor-Abstract-Group G Y)
        ( f))
      ( f)
      ( refl-htpy)

  right-unit-law-comp-equiv-Torsor-Abstract-Group :
    (f : equiv-Torsor-Abstract-Group G X Y) →
    Id
      ( comp-equiv-Torsor-Abstract-Group G X X Y f
        ( id-equiv-Torsor-Abstract-Group G X))
      ( f)
  right-unit-law-comp-equiv-Torsor-Abstract-Group f =
    eq-htpy-equiv-Torsor-Abstract-Group G X Y
      ( comp-equiv-Torsor-Abstract-Group G X X Y f
        ( id-equiv-Torsor-Abstract-Group G X))
      ( f)
      ( refl-htpy)

  left-inverse-law-comp-equiv-Torsor-Abstract-Group :
    (f : equiv-Torsor-Abstract-Group G X Y) →
    Id
      ( comp-equiv-Torsor-Abstract-Group G X Y X
        ( inv-equiv-Torsor-Abstract-Group G X Y f)
        ( f))
      ( id-equiv-Torsor-Abstract-Group G X)
  left-inverse-law-comp-equiv-Torsor-Abstract-Group f =
    eq-htpy-equiv-Torsor-Abstract-Group G X X
      ( comp-equiv-Torsor-Abstract-Group G X Y X
        ( inv-equiv-Torsor-Abstract-Group G X Y f)
        ( f))
      ( id-equiv-Torsor-Abstract-Group G X)
      ( is-retraction-map-inv-equiv (pr1 f))

  right-inverse-law-comp-equiv-Torsor-Abstract-Group :
    (f : equiv-Torsor-Abstract-Group G X Y) →
    Id
      ( comp-equiv-Torsor-Abstract-Group G Y X Y f
        ( inv-equiv-Torsor-Abstract-Group G X Y f))
      ( id-equiv-Torsor-Abstract-Group G Y)
  right-inverse-law-comp-equiv-Torsor-Abstract-Group f =
    eq-htpy-equiv-Torsor-Abstract-Group G Y Y
      ( comp-equiv-Torsor-Abstract-Group G Y X Y f
        ( inv-equiv-Torsor-Abstract-Group G X Y f))
      ( id-equiv-Torsor-Abstract-Group G Y)
      ( is-section-map-inv-equiv (pr1 f))

module _
  {l1 : Level} (G : Group l1)
  where

  preserves-mul-equiv-eq-Torsor-Abstract-Group :
    {l2 : Level} (X Y Z : Torsor-Abstract-Group G l2)
    (p : Id X Y) (q : Id Y Z) →
    Id
      ( equiv-eq-Torsor-Abstract-Group G X Z (p ∙ q))
      ( comp-equiv-Torsor-Abstract-Group G X Y Z
        ( equiv-eq-Torsor-Abstract-Group G Y Z q)
        ( equiv-eq-Torsor-Abstract-Group G X Y p))
  preserves-mul-equiv-eq-Torsor-Abstract-Group X .X Z refl q =
    inv ( right-unit-law-comp-equiv-Torsor-Abstract-Group G X Z
          ( equiv-eq-Torsor-Abstract-Group G X Z q))

module _
  {l1 : Level} (G : Group l1)
  where

  aut-principal-Torsor-Abstract-Group : Group l1
  pr1 (pr1 (pr1 aut-principal-Torsor-Abstract-Group)) =
    equiv-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
  pr2 (pr1 (pr1 aut-principal-Torsor-Abstract-Group)) =
    is-set-equiv-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
  pr1 (pr2 (pr1 aut-principal-Torsor-Abstract-Group)) =
    comp-equiv-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
  pr2 (pr2 (pr1 aut-principal-Torsor-Abstract-Group)) =
    associative-comp-equiv-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
  pr1 (pr1 (pr2 aut-principal-Torsor-Abstract-Group)) =
    id-equiv-Torsor-Abstract-Group G (principal-Torsor-Abstract-Group G)
  pr1 (pr2 (pr1 (pr2 aut-principal-Torsor-Abstract-Group))) =
    left-unit-law-comp-equiv-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
  pr2 (pr2 (pr1 (pr2 aut-principal-Torsor-Abstract-Group))) =
    right-unit-law-comp-equiv-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
  pr1 (pr2 (pr2 aut-principal-Torsor-Abstract-Group)) =
    inv-equiv-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
  pr1 (pr2 (pr2 (pr2 aut-principal-Torsor-Abstract-Group))) =
    left-inverse-law-comp-equiv-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
  pr2 (pr2 (pr2 (pr2 aut-principal-Torsor-Abstract-Group))) =
    right-inverse-law-comp-equiv-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
```

### The type `Torsor-Abstract-Group` is `0-connected`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : Torsor-Abstract-Group G l2)
  where

  mere-eq-Torsor-Abstract-Group :
    (Y : Torsor-Abstract-Group G l2) → mere-eq X Y
  mere-eq-Torsor-Abstract-Group Y =
    apply-universal-property-trunc-Prop
      ( pr2 X)
      ( mere-eq-Prop X Y)
      ( λ e →
        apply-universal-property-trunc-Prop
          ( pr2 Y)
          ( mere-eq-Prop X Y)
          ( λ f →
            unit-trunc-Prop
              ( eq-equiv-Torsor-Abstract-Group G X Y
                ( comp-equiv-Torsor-Abstract-Group G
                  ( X)
                  ( principal-Torsor-Abstract-Group G)
                  ( Y)
                  ( f)
                  ( inv-equiv-Torsor-Abstract-Group G
                    ( principal-Torsor-Abstract-Group G)
                    ( X)
                    ( e))))))

module _
  {l1 : Level} (G : Group l1)
  where

  is-0-connected-Torsor-Abstract-Group :
    is-0-connected (Torsor-Abstract-Group G l1)
  is-0-connected-Torsor-Abstract-Group =
    is-0-connected-mere-eq
      ( principal-Torsor-Abstract-Group G)
      ( mere-eq-Torsor-Abstract-Group G (principal-Torsor-Abstract-Group G))
```

### The group `aut-principal-Torsor-Abstract-Group` is isomorphic to `G`

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  Eq-Torsor-Abstract-Group :
    (X : Torsor-Abstract-Group G l1) → UU l1
  Eq-Torsor-Abstract-Group X = type-Torsor-Abstract-Group G X

  refl-Eq-Torsor-Abstract-Group :
    Eq-Torsor-Abstract-Group (principal-Torsor-Abstract-Group G)
  refl-Eq-Torsor-Abstract-Group = unit-Group G

  Eq-equiv-Torsor-Abstract-Group :
    (X : Torsor-Abstract-Group G l1) →
    equiv-Torsor-Abstract-Group G (principal-Torsor-Abstract-Group G) X →
    Eq-Torsor-Abstract-Group X
  Eq-equiv-Torsor-Abstract-Group X (pair e H) = map-equiv e (unit-Group G)

  preserves-mul-Eq-equiv-Torsor-Abstract-Group :
    (e f :
      equiv-Torsor-Abstract-Group G
        ( principal-Torsor-Abstract-Group G)
        ( principal-Torsor-Abstract-Group G)) →
    Id
      ( Eq-equiv-Torsor-Abstract-Group
        ( principal-Torsor-Abstract-Group G)
        ( comp-equiv-Torsor-Abstract-Group G
          ( principal-Torsor-Abstract-Group G)
          ( principal-Torsor-Abstract-Group G)
          ( principal-Torsor-Abstract-Group G)
          ( f)
          ( e)))
      ( mul-Group G
        ( Eq-equiv-Torsor-Abstract-Group
          ( principal-Torsor-Abstract-Group G)
          ( e))
        ( Eq-equiv-Torsor-Abstract-Group
          ( principal-Torsor-Abstract-Group G)
          ( f)))
  preserves-mul-Eq-equiv-Torsor-Abstract-Group (pair e H) (pair f K) =
    ( ap
      ( map-equiv f)
      ( inv (right-unit-law-mul-Group G (map-equiv e (unit-Group G))))) ∙
    ( K (map-equiv e (unit-Group G)) (unit-Group G))

  equiv-Eq-Torsor-Abstract-Group :
    Eq-Torsor-Abstract-Group (principal-Torsor-Abstract-Group G) →
    equiv-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
  pr1 (equiv-Eq-Torsor-Abstract-Group u) = equiv-mul-Group' G u
  pr2 (equiv-Eq-Torsor-Abstract-Group u) g x = associative-mul-Group G g x u

  is-section-equiv-Eq-Torsor-Abstract-Group :
    ( Eq-equiv-Torsor-Abstract-Group (principal-Torsor-Abstract-Group G) ∘
      equiv-Eq-Torsor-Abstract-Group) ~
    ( id)
  is-section-equiv-Eq-Torsor-Abstract-Group u = left-unit-law-mul-Group G u

  is-retraction-equiv-Eq-Torsor-Abstract-Group :
    ( equiv-Eq-Torsor-Abstract-Group ∘
      Eq-equiv-Torsor-Abstract-Group (principal-Torsor-Abstract-Group G)) ~
    ( id)
  is-retraction-equiv-Eq-Torsor-Abstract-Group e =
    eq-htpy-equiv-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
      ( equiv-Eq-Torsor-Abstract-Group
        ( Eq-equiv-Torsor-Abstract-Group (principal-Torsor-Abstract-Group G) e))
      ( e)
      ( λ g →
        ( inv (pr2 e g (unit-Group G))) ∙
        ( ap (map-equiv (pr1 e)) (right-unit-law-mul-Group G g)))

  abstract
    is-equiv-Eq-equiv-Torsor-Abstract-Group :
      (X : Torsor-Abstract-Group G l1) →
      is-equiv (Eq-equiv-Torsor-Abstract-Group X)
    is-equiv-Eq-equiv-Torsor-Abstract-Group X =
      apply-universal-property-trunc-Prop
        ( is-torsor-action-Torsor-Abstract-Group G X)
        ( is-equiv-Prop (Eq-equiv-Torsor-Abstract-Group X))
        ( λ e →
          tr
            ( λ Y → is-equiv (Eq-equiv-Torsor-Abstract-Group Y))
            ( eq-equiv-Torsor-Abstract-Group G
              ( principal-Torsor-Abstract-Group G)
              ( X)
              ( e))
            ( is-equiv-has-inverse
                equiv-Eq-Torsor-Abstract-Group
                is-section-equiv-Eq-Torsor-Abstract-Group
                is-retraction-equiv-Eq-Torsor-Abstract-Group))

  equiv-Eq-equiv-Torsor-Abstract-Group :
    (X : Torsor-Abstract-Group G l1) →
    Id (principal-Torsor-Abstract-Group G) X ≃ Eq-Torsor-Abstract-Group X
  equiv-Eq-equiv-Torsor-Abstract-Group X =
    ( pair
      ( Eq-equiv-Torsor-Abstract-Group X)
      ( is-equiv-Eq-equiv-Torsor-Abstract-Group X)) ∘e
    ( extensionality-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( X))

  preserves-mul-equiv-Eq-equiv-Torsor-Abstract-Group :
    ( p q :
      Id
        ( principal-Torsor-Abstract-Group G)
        ( principal-Torsor-Abstract-Group G)) →
    Id
      ( map-equiv
        ( equiv-Eq-equiv-Torsor-Abstract-Group
          ( principal-Torsor-Abstract-Group G))
        ( p ∙ q))
      ( mul-Group G
        ( map-equiv
          ( equiv-Eq-equiv-Torsor-Abstract-Group
            ( principal-Torsor-Abstract-Group G))
          ( p))
        ( map-equiv
          ( equiv-Eq-equiv-Torsor-Abstract-Group
            ( principal-Torsor-Abstract-Group G))
          ( q)))
  preserves-mul-equiv-Eq-equiv-Torsor-Abstract-Group p q =
    ( ap
      ( Eq-equiv-Torsor-Abstract-Group (principal-Torsor-Abstract-Group G))
      ( preserves-mul-equiv-eq-Torsor-Abstract-Group G
        ( principal-Torsor-Abstract-Group G)
        ( principal-Torsor-Abstract-Group G)
        ( principal-Torsor-Abstract-Group G)
        ( p)
        ( q))) ∙
    ( preserves-mul-Eq-equiv-Torsor-Abstract-Group
      ( equiv-eq-Torsor-Abstract-Group G
        ( principal-Torsor-Abstract-Group G)
        ( principal-Torsor-Abstract-Group G)
        ( p))
      ( equiv-eq-Torsor-Abstract-Group G
        ( principal-Torsor-Abstract-Group G)
        ( principal-Torsor-Abstract-Group G)
        ( q)))
```

### From torsors to concrete group

```agda
  ∞-group-Group : ∞-Group (lsuc l1)
  pr1 (pr1 ∞-group-Group) = Torsor-Abstract-Group G l1
  pr2 (pr1 ∞-group-Group) = principal-Torsor-Abstract-Group G
  pr2 ∞-group-Group = is-0-connected-Torsor-Abstract-Group G

  concrete-group-Group : Concrete-Group (lsuc l1)
  pr1 concrete-group-Group = ∞-group-Group
  pr2 concrete-group-Group =
    is-set-equiv
      ( type-Group G)
      ( equiv-Eq-equiv-Torsor-Abstract-Group
        ( principal-Torsor-Abstract-Group G))
      ( is-set-type-Group G)

  abstract-group-concrete-group-Group :
    type-iso-Group (abstract-group-Concrete-Group concrete-group-Group) G
  abstract-group-concrete-group-Group =
    iso-equiv-Group
      ( abstract-group-Concrete-Group concrete-group-Group)
      ( G)
      ( pair
        ( equiv-Eq-equiv-Torsor-Abstract-Group
          ( principal-Torsor-Abstract-Group G))
        ( preserves-mul-equiv-Eq-equiv-Torsor-Abstract-Group))

{-
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  map-Torsor-Abstract-Group :
    type-hom-Group G H → Torsor-Abstract-Group G l1 → Torsor-Abstract-Group H l2
  pr1 (pr1 (map-Torsor-Abstract-Group f X)) = {!!}
  pr2 (pr1 (map-Torsor-Abstract-Group f X)) = {!!}
  pr2 (map-Torsor-Abstract-Group f X) = {!!}
-}
```
