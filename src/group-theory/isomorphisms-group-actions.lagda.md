# Isomorphisms of group actions

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.isomorphisms-group-actions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories funext

open import foundation.commuting-squares-of-maps funext
open import foundation.contractible-types funext
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.function-extensionality funext

open import foundation.functoriality-dependent-pair-types funext
open import foundation.identity-types funext
open import foundation.logical-equivalences funext
open import foundation.propositions funext
open import foundation.subtypes funext
open import foundation.torsorial-type-families funext
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.equivalences-group-actions funext
open import group-theory.group-actions funext
open import group-theory.groups funext
open import group-theory.homomorphisms-group-actions funext
open import group-theory.precategory-of-group-actions funext
```

</details>

## Definitions

### The predicate of being an isomorphism of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  is-iso-action-Group :
    (f : hom-action-Group G X Y) → UU (l1 ⊔ l2 ⊔ l3)
  is-iso-action-Group =
    is-iso-Large-Precategory (action-Group-Large-Precategory G) {X = X} {Y = Y}

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  (f : hom-action-Group G X Y) (is-iso-f : is-iso-action-Group G X Y f)
  where

  hom-inv-is-iso-action-Group : hom-action-Group G Y X
  hom-inv-is-iso-action-Group =
    hom-inv-is-iso-Large-Precategory
      ( action-Group-Large-Precategory G) {X = X} {Y = Y} f is-iso-f

  map-hom-inv-is-iso-action-Group :
    type-action-Group G Y → type-action-Group G X
  map-hom-inv-is-iso-action-Group =
    map-hom-action-Group G Y X hom-inv-is-iso-action-Group

  is-section-hom-inv-is-iso-action-Group :
    ( comp-hom-action-Group G Y X Y f hom-inv-is-iso-action-Group) ＝
    ( id-hom-action-Group G Y)
  is-section-hom-inv-is-iso-action-Group =
    is-section-hom-inv-is-iso-Large-Precategory
      ( action-Group-Large-Precategory G) {X = X} {Y = Y} f is-iso-f

  is-retraction-hom-inv-is-iso-action-Group :
    ( comp-hom-action-Group G X Y X hom-inv-is-iso-action-Group f) ＝
    ( id-hom-action-Group G X)
  is-retraction-hom-inv-is-iso-action-Group =
    is-retraction-hom-inv-is-iso-Large-Precategory
      ( action-Group-Large-Precategory G) {X = X} {Y = Y} f is-iso-f
```

### The type of isomorphisms of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (X : action-Group G l2)
  (Y : action-Group G l3)
  where

  iso-action-Group : UU (l1 ⊔ l2 ⊔ l3)
  iso-action-Group =
    iso-Large-Precategory (action-Group-Large-Precategory G) X Y

  hom-iso-action-Group :
    iso-action-Group → hom-action-Group G X Y
  hom-iso-action-Group =
    hom-iso-Large-Precategory (action-Group-Large-Precategory G) {X = X} {Y = Y}

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
    preserves-action-hom-action-Group G X Y (hom-iso-action-Group f)

  hom-inv-iso-action-Group :
    iso-action-Group → hom-action-Group G Y X
  hom-inv-iso-action-Group =
    hom-inv-iso-Large-Precategory
      ( action-Group-Large-Precategory G) {X = X} {Y = Y}

  map-hom-inv-iso-action-Group :
    iso-action-Group →
    type-action-Group G Y → type-action-Group G X
  map-hom-inv-iso-action-Group f =
    map-hom-action-Group G Y X (hom-inv-iso-action-Group f)

  is-section-hom-inv-iso-action-Group :
    (f : iso-action-Group) →
    ( comp-hom-action-Group G Y X Y
      ( hom-iso-action-Group f)
      ( hom-inv-iso-action-Group f)) ＝
    ( id-hom-action-Group G Y)
  is-section-hom-inv-iso-action-Group =
    is-section-hom-inv-iso-Large-Precategory
      ( action-Group-Large-Precategory G) {X = X} {Y = Y}

  is-retraction-hom-inv-iso-action-Group :
    (f : iso-action-Group) →
    ( comp-hom-action-Group G X Y X
      ( hom-inv-iso-action-Group f)
      ( hom-iso-action-Group f)) ＝
    ( id-hom-action-Group G X)
  is-retraction-hom-inv-iso-action-Group =
    is-retraction-hom-inv-iso-Large-Precategory
      ( action-Group-Large-Precategory G) {X = X} {Y = Y}

  is-iso-iso-action-Group :
    (f : iso-action-Group) → is-iso-action-Group G X Y (hom-iso-action-Group f)
  is-iso-iso-action-Group =
    is-iso-iso-Large-Precategory
      ( action-Group-Large-Precategory G) {X = X} {Y = Y}
```

## Properties

### Isomorphisms of group actions are equivalent to equivalences of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  (f : hom-action-Group G X Y)
  where

  is-equiv-hom-is-iso-action-Group :
    is-iso-action-Group G X Y f → is-equiv-hom-action-Group G X Y f
  is-equiv-hom-is-iso-action-Group is-iso-f =
    is-equiv-is-invertible
      ( map-hom-inv-is-iso-action-Group G X Y f is-iso-f)
      ( htpy-eq-hom-action-Group G Y Y
        ( comp-hom-action-Group G Y X Y
          ( f)
          ( hom-inv-is-iso-action-Group G X Y f is-iso-f))
        ( id-hom-action-Group G Y)
        ( is-section-hom-inv-is-iso-action-Group G X Y f is-iso-f))
      ( htpy-eq-hom-action-Group G X X
        ( comp-hom-action-Group G X Y X
          ( hom-inv-is-iso-action-Group G X Y f is-iso-f)
          ( f))
        ( id-hom-action-Group G X)
        ( is-retraction-hom-inv-is-iso-action-Group G X Y f is-iso-f))

  is-iso-is-equiv-hom-action-Group :
    is-equiv-hom-action-Group G X Y f → is-iso-action-Group G X Y f
  pr1 (pr1 (is-iso-is-equiv-hom-action-Group is-equiv-f)) =
    map-inv-is-equiv is-equiv-f
  pr2 (pr1 (is-iso-is-equiv-hom-action-Group is-equiv-f)) =
    preserves-action-map-inv-is-equiv-hom-action-Group G X Y f is-equiv-f
  pr1 (pr2 (is-iso-is-equiv-hom-action-Group is-equiv-f)) =
    eq-type-subtype
      ( preserves-action-prop-Group G Y Y)
      ( eq-htpy (is-section-map-inv-is-equiv is-equiv-f))
  pr2 (pr2 (is-iso-is-equiv-hom-action-Group is-equiv-f)) =
    eq-type-subtype
      ( preserves-action-prop-Group G X X)
      ( eq-htpy (is-retraction-map-inv-is-equiv is-equiv-f))

  is-equiv-is-equiv-hom-is-iso-action-Group :
    is-equiv is-equiv-hom-is-iso-action-Group
  is-equiv-is-equiv-hom-is-iso-action-Group =
    is-equiv-has-converse-is-prop
      ( is-prop-is-iso-Large-Precategory
        ( action-Group-Large-Precategory G) {X = X} {Y = Y} f)
      ( is-property-is-equiv (map-hom-action-Group G X Y f))
      ( is-iso-is-equiv-hom-action-Group)

  is-equiv-is-iso-is-equiv-hom-action-Group :
    is-equiv is-iso-is-equiv-hom-action-Group
  is-equiv-is-iso-is-equiv-hom-action-Group =
    is-equiv-has-converse-is-prop
      ( is-property-is-equiv (map-hom-action-Group G X Y f))
      ( is-prop-is-iso-Large-Precategory
        ( action-Group-Large-Precategory G) {X = X} {Y = Y} f)
      ( is-equiv-hom-is-iso-action-Group)

  equiv-is-equiv-hom-is-iso-action-Group :
    is-iso-action-Group G X Y f ≃ is-equiv-hom-action-Group G X Y f
  pr1 equiv-is-equiv-hom-is-iso-action-Group =
    is-equiv-hom-is-iso-action-Group
  pr2 equiv-is-equiv-hom-is-iso-action-Group =
    is-equiv-is-equiv-hom-is-iso-action-Group

  equiv-is-iso-is-equiv-hom-action-Group :
    is-equiv-hom-action-Group G X Y f ≃ is-iso-action-Group G X Y f
  pr1 equiv-is-iso-is-equiv-hom-action-Group =
    is-iso-is-equiv-hom-action-Group
  pr2 equiv-is-iso-is-equiv-hom-action-Group =
    is-equiv-is-iso-is-equiv-hom-action-Group

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  (f : iso-action-Group G X Y)
  where

  is-equiv-map-iso-action-Group : is-equiv (map-iso-action-Group G X Y f)
  is-equiv-map-iso-action-Group =
    is-equiv-hom-is-iso-action-Group G X Y
      ( hom-iso-action-Group G X Y f)
      ( is-iso-iso-action-Group G X Y f)

  equiv-iso-action-Group : equiv-action-Group G X Y
  pr1 (pr1 equiv-iso-action-Group) = map-iso-action-Group G X Y f
  pr2 (pr1 equiv-iso-action-Group) = is-equiv-map-iso-action-Group
  pr2 equiv-iso-action-Group = preserves-action-iso-action-Group G X Y f

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  equiv-equiv-iso-action-Group :
    iso-action-Group G X Y ≃ equiv-action-Group G X Y
  equiv-equiv-iso-action-Group =
    equiv-right-swap-Σ ∘e
    equiv-tot (equiv-is-equiv-hom-is-iso-action-Group G X Y)

  equiv-iso-equiv-action-Group :
    equiv-action-Group G X Y ≃ iso-action-Group G X Y
  equiv-iso-equiv-action-Group =
    equiv-tot (equiv-is-iso-is-equiv-hom-action-Group G X Y) ∘e
    equiv-right-swap-Σ
```

### Isomorphisms characterize equality of `G`-sets

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  is-torsorial-iso-action-Group : is-torsorial (iso-action-Group {l3 = l2} G X)
  is-torsorial-iso-action-Group =
    is-contr-equiv
      ( Σ (action-Group G l2) (equiv-action-Group G X))
      ( equiv-tot (equiv-equiv-iso-action-Group G X))
      ( is-torsorial-equiv-action-Group G X)
```
