# Torsors of abstract groups

```agda
module group-theory.torsors where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
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

A **torsor** of a [group](group-theory.groups.md) `G` is a
[group action](group-theory.group-actions.md) which is
[merely equivalent](foundation.mere-equivalences.md) to the
[principal group action](group-theory.principal-group-actions.md) of `G`.

## Definitions

### The predicate of being a torsor

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  is-torsor-prop-action-Group : Prop (l1 ⊔ l2)
  is-torsor-prop-action-Group =
    mere-equiv-prop-action-Group G (principal-action-Group G) X

  is-torsor-Group : UU (l1 ⊔ l2)
  is-torsor-Group = type-Prop is-torsor-prop-action-Group

  is-prop-is-torsor-Group : is-prop is-torsor-Group
  is-prop-is-torsor-Group = is-prop-type-Prop is-torsor-prop-action-Group
```

### The type of torsors

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  Torsor-Group : (l : Level) → UU (l1 ⊔ lsuc l)
  Torsor-Group l = Σ (action-Group G l) (is-torsor-Group G)

module _
  {l1 l : Level} (G : Group l1) (X : Torsor-Group G l)
  where

  action-Torsor-Group : action-Group G l
  action-Torsor-Group = pr1 X

  set-Torsor-Group : Set l
  set-Torsor-Group = set-action-Group G action-Torsor-Group

  type-Torsor-Group : UU l
  type-Torsor-Group = type-Set set-Torsor-Group

  is-set-type-Torsor-Group : is-set type-Torsor-Group
  is-set-type-Torsor-Group = is-set-type-Set set-Torsor-Group

  mul-hom-Torsor-Group : hom-Group G (symmetric-Group set-Torsor-Group)
  mul-hom-Torsor-Group = pr2 action-Torsor-Group

  equiv-mul-Torsor-Group : type-Group G → type-Torsor-Group ≃ type-Torsor-Group
  equiv-mul-Torsor-Group = equiv-mul-action-Group G action-Torsor-Group

  mul-Torsor-Group : type-Group G → type-Torsor-Group → type-Torsor-Group
  mul-Torsor-Group = mul-action-Group G action-Torsor-Group

  is-torsor-action-Torsor-Group : is-torsor-Group G action-Torsor-Group
  is-torsor-action-Torsor-Group = pr2 X
```

### Principal torsor

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  principal-Torsor-Group : Torsor-Group G l1
  pr1 principal-Torsor-Group = principal-action-Group G
  pr2 principal-Torsor-Group =
    unit-trunc-Prop (id-equiv-action-Group G (principal-action-Group G))
```

## Properties

### Characterization of the identity type of `Torsor-Group`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : Torsor-Group G l2)
  where

  equiv-Torsor-Group :
    {l3 : Level} (Y : Torsor-Group G l3) → UU (l1 ⊔ l2 ⊔ l3)
  equiv-Torsor-Group Y =
    equiv-action-Group G (action-Torsor-Group G X) (action-Torsor-Group G Y)

  id-equiv-Torsor-Group : equiv-Torsor-Group X
  id-equiv-Torsor-Group = id-equiv-action-Group G (action-Torsor-Group G X)

  equiv-eq-Torsor-Group :
    (Y : Torsor-Group G l2) → X ＝ Y → equiv-Torsor-Group Y
  equiv-eq-Torsor-Group .X refl = id-equiv-Torsor-Group

  is-torsorial-equiv-Torsor-Group :
    is-torsorial equiv-Torsor-Group
  is-torsorial-equiv-Torsor-Group =
    is-torsorial-Eq-subtype
      ( is-torsorial-equiv-action-Group G (action-Torsor-Group G X))
      ( is-prop-is-torsor-Group G)
      ( action-Torsor-Group G X)
      ( id-equiv-Torsor-Group)
      ( is-torsor-action-Torsor-Group G X)

  is-equiv-equiv-eq-Torsor-Group :
    (Y : Torsor-Group G l2) →
    is-equiv (equiv-eq-Torsor-Group Y)
  is-equiv-equiv-eq-Torsor-Group =
    fundamental-theorem-id
      is-torsorial-equiv-Torsor-Group
      equiv-eq-Torsor-Group

  eq-equiv-Torsor-Group :
    (Y : Torsor-Group G l2) → equiv-Torsor-Group Y → X ＝ Y
  eq-equiv-Torsor-Group Y =
    map-inv-is-equiv (is-equiv-equiv-eq-Torsor-Group Y)

  extensionality-Torsor-Group :
    (Y : Torsor-Group G l2) → (X ＝ Y) ≃ equiv-Torsor-Group Y
  pr1 (extensionality-Torsor-Group Y) = equiv-eq-Torsor-Group Y
  pr2 (extensionality-Torsor-Group Y) = is-equiv-equiv-eq-Torsor-Group Y
```

### Characterization of the identity type of equivalences between `Torsor-Group`

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Torsor-Group G l2)
  (Y : Torsor-Group G l3)
  (e : equiv-Torsor-Group G X Y)
  where

  htpy-equiv-Torsor-Group :
    equiv-Torsor-Group G X Y → UU (l2 ⊔ l3)
  htpy-equiv-Torsor-Group =
    htpy-equiv-action-Group G
      ( action-Torsor-Group G X)
      ( action-Torsor-Group G Y)
      ( e)

  refl-htpy-equiv-Torsor-Group :
    htpy-equiv-Torsor-Group e
  refl-htpy-equiv-Torsor-Group =
    refl-htpy-equiv-action-Group G
      ( action-Torsor-Group G X)
      ( action-Torsor-Group G Y)
      ( e)

  htpy-eq-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    e ＝ f → htpy-equiv-Torsor-Group f
  htpy-eq-equiv-Torsor-Group .e refl =
    refl-htpy-equiv-Torsor-Group

  is-torsorial-htpy-equiv-Torsor-Group :
    is-torsorial htpy-equiv-Torsor-Group
  is-torsorial-htpy-equiv-Torsor-Group =
    is-torsorial-htpy-equiv-action-Group G
      ( action-Torsor-Group G X)
      ( action-Torsor-Group G Y)
      ( e)

  is-equiv-htpy-eq-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    is-equiv (htpy-eq-equiv-Torsor-Group f)
  is-equiv-htpy-eq-equiv-Torsor-Group =
    fundamental-theorem-id
      is-torsorial-htpy-equiv-Torsor-Group
      htpy-eq-equiv-Torsor-Group

  extensionality-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    (e ＝ f) ≃ htpy-equiv-Torsor-Group f
  pr1 (extensionality-equiv-Torsor-Group f) =
    htpy-eq-equiv-Torsor-Group f
  pr2 (extensionality-equiv-Torsor-Group f) =
    is-equiv-htpy-eq-equiv-Torsor-Group f

  eq-htpy-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) → htpy-equiv-Torsor-Group f → e ＝ f
  eq-htpy-equiv-Torsor-Group f =
    map-inv-is-equiv (is-equiv-htpy-eq-equiv-Torsor-Group f)
```

### Definition of the group `aut-principal-Torsor-Group` from a `Torsor-Group`

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Torsor-Group G l2)
  (Y : Torsor-Group G l3)
  where

  is-set-equiv-Torsor-Group :
    is-set (equiv-Torsor-Group G X Y)
  is-set-equiv-Torsor-Group e f =
    is-prop-equiv
      ( extensionality-equiv-Torsor-Group G X Y e f)
      ( is-prop-Π
        ( λ x →
          is-set-type-Torsor-Group G Y
            ( map-equiv (pr1 e) x)
            ( map-equiv (pr1 f) x)))

module _
  {l1 l2 l3 l4 : Level} (G : Group l1)
  (X : Torsor-Group G l2)
  (Y : Torsor-Group G l3)
  (Z : Torsor-Group G l4)
  where

  comp-equiv-Torsor-Group :
    equiv-Torsor-Group G Y Z →
    equiv-Torsor-Group G X Y →
    equiv-Torsor-Group G X Z
  comp-equiv-Torsor-Group =
    comp-equiv-action-Group G
      ( action-Torsor-Group G X)
      ( action-Torsor-Group G Y)
      ( action-Torsor-Group G Z)

  comp-equiv-Torsor-Group' :
    equiv-Torsor-Group G X Y →
    equiv-Torsor-Group G Y Z →
    equiv-Torsor-Group G X Z
  comp-equiv-Torsor-Group' e f =
    comp-equiv-Torsor-Group f e

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Torsor-Group G l2)
  (Y : Torsor-Group G l3)
  where

  inv-equiv-Torsor-Group :
    equiv-Torsor-Group G X Y →
    equiv-Torsor-Group G Y X
  inv-equiv-Torsor-Group =
    inv-equiv-action-Group G
      ( action-Torsor-Group G X)
      ( action-Torsor-Group G Y)

module _
  {l1 l2 l3 l4 l5 : Level} (G : Group l1)
  (X1 : Torsor-Group G l2)
  (X2 : Torsor-Group G l3)
  (X3 : Torsor-Group G l4)
  (X4 : Torsor-Group G l5)
  where

  associative-comp-equiv-Torsor-Group :
    (h : equiv-Torsor-Group G X3 X4)
    (g : equiv-Torsor-Group G X2 X3)
    (f : equiv-Torsor-Group G X1 X2) →
    ( comp-equiv-Torsor-Group G X1 X2 X4
      ( comp-equiv-Torsor-Group G X2 X3 X4 h g)
      ( f)) ＝
    ( comp-equiv-Torsor-Group G X1 X3 X4 h
      ( comp-equiv-Torsor-Group G X1 X2 X3 g f))
  associative-comp-equiv-Torsor-Group h g f =
    eq-htpy-equiv-Torsor-Group G X1 X4
      ( comp-equiv-Torsor-Group G X1 X2 X4
        ( comp-equiv-Torsor-Group G X2 X3 X4 h g)
        ( f))
      ( comp-equiv-Torsor-Group G X1 X3 X4 h
        ( comp-equiv-Torsor-Group G X1 X2 X3 g f))
      ( refl-htpy)

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Torsor-Group G l2)
  (Y : Torsor-Group G l3)
  where

  left-unit-law-comp-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    ( comp-equiv-Torsor-Group G X Y Y (id-equiv-Torsor-Group G Y) f) ＝ f
  left-unit-law-comp-equiv-Torsor-Group f =
    eq-htpy-equiv-Torsor-Group G X Y
      ( comp-equiv-Torsor-Group G X Y Y
        ( id-equiv-Torsor-Group G Y)
        ( f))
      ( f)
      ( refl-htpy)

  right-unit-law-comp-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    ( comp-equiv-Torsor-Group G X X Y f (id-equiv-Torsor-Group G X)) ＝ f
  right-unit-law-comp-equiv-Torsor-Group f =
    eq-htpy-equiv-Torsor-Group G X Y
      ( comp-equiv-Torsor-Group G X X Y f
        ( id-equiv-Torsor-Group G X))
      ( f)
      ( refl-htpy)

  left-inverse-law-comp-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    ( comp-equiv-Torsor-Group G X Y X (inv-equiv-Torsor-Group G X Y f) f) ＝
    ( id-equiv-Torsor-Group G X)
  left-inverse-law-comp-equiv-Torsor-Group f =
    eq-htpy-equiv-Torsor-Group G X X
      ( comp-equiv-Torsor-Group G X Y X
        ( inv-equiv-Torsor-Group G X Y f)
        ( f))
      ( id-equiv-Torsor-Group G X)
      ( is-retraction-map-inv-equiv (pr1 f))

  right-inverse-law-comp-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    ( comp-equiv-Torsor-Group G Y X Y f (inv-equiv-Torsor-Group G X Y f)) ＝
    ( id-equiv-Torsor-Group G Y)
  right-inverse-law-comp-equiv-Torsor-Group f =
    eq-htpy-equiv-Torsor-Group G Y Y
      ( comp-equiv-Torsor-Group G Y X Y f (inv-equiv-Torsor-Group G X Y f))
      ( id-equiv-Torsor-Group G Y)
      ( is-section-map-inv-equiv (pr1 f))

module _
  {l1 : Level} (G : Group l1)
  where

  preserves-mul-equiv-eq-Torsor-Group :
    {l2 : Level} (X Y Z : Torsor-Group G l2)
    (p : X ＝ Y) (q : Y ＝ Z) →
    ( equiv-eq-Torsor-Group G X Z (p ∙ q)) ＝
    ( comp-equiv-Torsor-Group G X Y Z
      ( equiv-eq-Torsor-Group G Y Z q)
      ( equiv-eq-Torsor-Group G X Y p))
  preserves-mul-equiv-eq-Torsor-Group X .X Z refl q =
    inv
      ( right-unit-law-comp-equiv-Torsor-Group G X Z
        ( equiv-eq-Torsor-Group G X Z q))

module _
  {l1 : Level} (G : Group l1)
  where

  aut-principal-Torsor-Group : Group l1
  pr1 (pr1 (pr1 aut-principal-Torsor-Group)) =
    equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr2 (pr1 (pr1 aut-principal-Torsor-Group)) =
    is-set-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr1 (pr2 (pr1 aut-principal-Torsor-Group)) =
    comp-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr2 (pr2 (pr1 aut-principal-Torsor-Group)) =
    associative-comp-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr1 (pr1 (pr2 aut-principal-Torsor-Group)) =
    id-equiv-Torsor-Group G (principal-Torsor-Group G)
  pr1 (pr2 (pr1 (pr2 aut-principal-Torsor-Group))) =
    left-unit-law-comp-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr2 (pr2 (pr1 (pr2 aut-principal-Torsor-Group))) =
    right-unit-law-comp-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr1 (pr2 (pr2 aut-principal-Torsor-Group)) =
    inv-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr1 (pr2 (pr2 (pr2 aut-principal-Torsor-Group))) =
    left-inverse-law-comp-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr2 (pr2 (pr2 (pr2 aut-principal-Torsor-Group))) =
    right-inverse-law-comp-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
```

### The type `Torsor-Group` is `0-connected`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : Torsor-Group G l2)
  where

  mere-eq-Torsor-Group :
    (Y : Torsor-Group G l2) → mere-eq X Y
  mere-eq-Torsor-Group Y =
    map-binary-trunc-Prop
      ( λ e f →
        eq-equiv-Torsor-Group G X Y
          ( comp-equiv-Torsor-Group G
            ( X)
            ( principal-Torsor-Group G)
            ( Y)
            ( f)
            ( inv-equiv-Torsor-Group G
              ( principal-Torsor-Group G)
              ( X)
              ( e))))
      ( pr2 X)
      ( pr2 Y)

module _
  {l1 : Level} (G : Group l1)
  where

  is-0-connected-Torsor-Group :
    is-0-connected (Torsor-Group G l1)
  is-0-connected-Torsor-Group =
    is-0-connected-mere-eq
      ( principal-Torsor-Group G)
      ( mere-eq-Torsor-Group G (principal-Torsor-Group G))
```

### The group `aut-principal-Torsor-Group` is isomorphic to `G`

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  Eq-Torsor-Group :
    (X : Torsor-Group G l1) → UU l1
  Eq-Torsor-Group X = type-Torsor-Group G X

  refl-Eq-Torsor-Group :
    Eq-Torsor-Group (principal-Torsor-Group G)
  refl-Eq-Torsor-Group = unit-Group G

  Eq-equiv-Torsor-Group :
    (X : Torsor-Group G l1) →
    equiv-Torsor-Group G (principal-Torsor-Group G) X →
    Eq-Torsor-Group X
  Eq-equiv-Torsor-Group X (e , H) = map-equiv e (unit-Group G)

  preserves-mul-Eq-equiv-Torsor-Group :
    ( e f :
      equiv-Torsor-Group G
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)) →
    ( Eq-equiv-Torsor-Group
      ( principal-Torsor-Group G)
      ( comp-equiv-Torsor-Group G
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)
        ( f)
        ( e))) ＝
    ( mul-Group G
      ( Eq-equiv-Torsor-Group
        ( principal-Torsor-Group G)
        ( e))
      ( Eq-equiv-Torsor-Group
        ( principal-Torsor-Group G)
        ( f)))
  preserves-mul-Eq-equiv-Torsor-Group (e , H) (f , K) =
    ( ap
      ( map-equiv f)
      ( inv (right-unit-law-mul-Group G (map-equiv e (unit-Group G))))) ∙
    ( K (map-equiv e (unit-Group G)) (unit-Group G))

  equiv-Eq-Torsor-Group :
    Eq-Torsor-Group (principal-Torsor-Group G) →
    equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr1 (equiv-Eq-Torsor-Group u) = equiv-mul-Group' G u
  pr2 (equiv-Eq-Torsor-Group u) g x = associative-mul-Group G g x u

  is-section-equiv-Eq-Torsor-Group :
    ( Eq-equiv-Torsor-Group (principal-Torsor-Group G) ∘
      equiv-Eq-Torsor-Group) ~
    ( id)
  is-section-equiv-Eq-Torsor-Group u = left-unit-law-mul-Group G u

  is-retraction-equiv-Eq-Torsor-Group :
    is-retraction
      ( Eq-equiv-Torsor-Group (principal-Torsor-Group G))
      ( equiv-Eq-Torsor-Group)
  is-retraction-equiv-Eq-Torsor-Group e =
    eq-htpy-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
      ( equiv-Eq-Torsor-Group
        ( Eq-equiv-Torsor-Group (principal-Torsor-Group G) e))
      ( e)
      ( λ g →
        ( inv (pr2 e g (unit-Group G))) ∙
        ( ap (map-equiv (pr1 e)) (right-unit-law-mul-Group G g)))

  abstract
    is-equiv-Eq-equiv-Torsor-Group :
      (X : Torsor-Group G l1) →
      is-equiv (Eq-equiv-Torsor-Group X)
    is-equiv-Eq-equiv-Torsor-Group X =
      apply-universal-property-trunc-Prop
        ( is-torsor-action-Torsor-Group G X)
        ( is-equiv-Prop (Eq-equiv-Torsor-Group X))
        ( λ e →
          tr
            ( λ Y → is-equiv (Eq-equiv-Torsor-Group Y))
            ( eq-equiv-Torsor-Group G (principal-Torsor-Group G) X e)
            ( is-equiv-is-invertible
                equiv-Eq-Torsor-Group
                is-section-equiv-Eq-Torsor-Group
                is-retraction-equiv-Eq-Torsor-Group))

  equiv-Eq-equiv-Torsor-Group :
    (X : Torsor-Group G l1) →
    (principal-Torsor-Group G ＝ X) ≃ Eq-Torsor-Group X
  equiv-Eq-equiv-Torsor-Group X =
    ( Eq-equiv-Torsor-Group X , is-equiv-Eq-equiv-Torsor-Group X) ∘e
    ( extensionality-Torsor-Group G (principal-Torsor-Group G) X)

  preserves-mul-equiv-Eq-equiv-Torsor-Group :
    { p q : principal-Torsor-Group G ＝ principal-Torsor-Group G} →
    Id
      ( map-equiv
        ( equiv-Eq-equiv-Torsor-Group (principal-Torsor-Group G))
        ( p ∙ q))
      ( mul-Group G
        ( map-equiv
          ( equiv-Eq-equiv-Torsor-Group (principal-Torsor-Group G))
          ( p))
        ( map-equiv
          ( equiv-Eq-equiv-Torsor-Group (principal-Torsor-Group G))
          ( q)))
  preserves-mul-equiv-Eq-equiv-Torsor-Group {p} {q} =
    ( ap
      ( Eq-equiv-Torsor-Group (principal-Torsor-Group G))
      ( preserves-mul-equiv-eq-Torsor-Group G
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)
        ( p)
        ( q))) ∙
    ( preserves-mul-Eq-equiv-Torsor-Group
      ( equiv-eq-Torsor-Group G
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)
        ( p))
      ( equiv-eq-Torsor-Group G
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)
        ( q)))
```

### From torsors to concrete group

```agda
  ∞-group-Group : ∞-Group (lsuc l1)
  pr1 (pr1 ∞-group-Group) = Torsor-Group G l1
  pr2 (pr1 ∞-group-Group) = principal-Torsor-Group G
  pr2 ∞-group-Group = is-0-connected-Torsor-Group G

  concrete-group-Group : Concrete-Group (lsuc l1)
  pr1 concrete-group-Group = ∞-group-Group
  pr2 concrete-group-Group =
    is-set-equiv
      ( type-Group G)
      ( equiv-Eq-equiv-Torsor-Group (principal-Torsor-Group G))
      ( is-set-type-Group G)

  classifying-type-Group : UU (lsuc l1)
  classifying-type-Group = classifying-type-Concrete-Group concrete-group-Group

  shape-Group : classifying-type-Group
  shape-Group = shape-Concrete-Group concrete-group-Group

  is-0-connected-classifying-type-Group : is-0-connected classifying-type-Group
  is-0-connected-classifying-type-Group =
    is-0-connected-classifying-type-Concrete-Group concrete-group-Group

  group-concrete-group-Group :
    iso-Group (group-Concrete-Group concrete-group-Group) G
  group-concrete-group-Group =
    iso-equiv-Group
      ( group-Concrete-Group concrete-group-Group)
      ( G)
      ( ( equiv-Eq-equiv-Torsor-Group (principal-Torsor-Group G)) ,
        ( λ {p} {q} → preserves-mul-equiv-Eq-equiv-Torsor-Group {p} {q}))
```
