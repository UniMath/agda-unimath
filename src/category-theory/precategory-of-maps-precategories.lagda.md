# The precategory of maps and natural transformations between two precategories

```agda
module category-theory.precategory-of-maps-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.natural-isomorphisms-maps-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality-axiom
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels
```

</details>

## Idea

[Maps](category-theory.maps-precategories.md) between
[precategories](category-theory.precategories.md) and
[natural transformations](category-theory.natural-transformations-maps-precategories.md)
between them introduce a new precategory whose identity map and composition
structure are inherited pointwise from the codomain precategory. This is called
the **precategory of maps**.

## Definitions

### The precategory of maps and natural transformations between precategories

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  comp-hom-map-precategory-Precategory :
    {F G H : map-Precategory C D} →
    natural-transformation-map-Precategory C D G H →
    natural-transformation-map-Precategory C D F G →
    natural-transformation-map-Precategory C D F H
  comp-hom-map-precategory-Precategory {F} {G} {H} =
    comp-natural-transformation-map-Precategory C D F G H

  associative-comp-hom-map-precategory-Precategory :
    {F G H I : map-Precategory C D}
    (h : natural-transformation-map-Precategory C D H I)
    (g : natural-transformation-map-Precategory C D G H)
    (f : natural-transformation-map-Precategory C D F G) →
    comp-natural-transformation-map-Precategory C D F G I
      ( comp-natural-transformation-map-Precategory C D G H I h g)
      ( f) ＝
    comp-natural-transformation-map-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-map-Precategory C D F G H g f)
  associative-comp-hom-map-precategory-Precategory {F} {G} {H} {I} h g f =
    associative-comp-natural-transformation-map-Precategory
      C D F G H I f g h

  involutive-eq-associative-comp-hom-map-precategory-Precategory :
    {F G H I : map-Precategory C D}
    (h : natural-transformation-map-Precategory C D H I)
    (g : natural-transformation-map-Precategory C D G H)
    (f : natural-transformation-map-Precategory C D F G) →
    comp-natural-transformation-map-Precategory C D F G I
      ( comp-natural-transformation-map-Precategory C D G H I h g)
      ( f) ＝ⁱ
    comp-natural-transformation-map-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-map-Precategory C D F G H g f)
  involutive-eq-associative-comp-hom-map-precategory-Precategory
    { F} {G} {H} {I} h g f =
    involutive-eq-associative-comp-natural-transformation-map-Precategory
      C D F G H I f g h

  associative-composition-operation-map-precategory-Precategory :
    associative-composition-operation-binary-family-Set
      ( natural-transformation-map-set-Precategory C D)
  pr1 associative-composition-operation-map-precategory-Precategory
    {F} {G} {H} =
    comp-hom-map-precategory-Precategory {F} {G} {H}
  pr2
    associative-composition-operation-map-precategory-Precategory
      {F} {G} {H} {I} h g f =
    involutive-eq-associative-comp-hom-map-precategory-Precategory
      { F} {G} {H} {I} h g f

  id-hom-map-precategory-Precategory :
    (F : map-Precategory C D) → natural-transformation-map-Precategory C D F F
  id-hom-map-precategory-Precategory =
    id-natural-transformation-map-Precategory C D

  left-unit-law-comp-hom-map-precategory-Precategory :
    {F G : map-Precategory C D}
    (α : natural-transformation-map-Precategory C D F G) →
    ( comp-natural-transformation-map-Precategory C D F G G
      ( id-natural-transformation-map-Precategory C D G) α) ＝
    ( α)
  left-unit-law-comp-hom-map-precategory-Precategory {F} {G} =
    left-unit-law-comp-natural-transformation-map-Precategory C D F G

  right-unit-law-comp-hom-map-precategory-Precategory :
    {F G : map-Precategory C D}
    (α : natural-transformation-map-Precategory C D F G) →
    ( comp-natural-transformation-map-Precategory C D F F G
        α (id-natural-transformation-map-Precategory C D F)) ＝
    ( α)
  right-unit-law-comp-hom-map-precategory-Precategory {F} {G} =
    right-unit-law-comp-natural-transformation-map-Precategory C D F G

  is-unital-composition-operation-map-precategory-Precategory :
    is-unital-composition-operation-binary-family-Set
      ( natural-transformation-map-set-Precategory C D)
      ( comp-hom-map-precategory-Precategory)
  pr1 is-unital-composition-operation-map-precategory-Precategory =
    id-hom-map-precategory-Precategory
  pr1
    ( pr2 is-unital-composition-operation-map-precategory-Precategory)
    { F} {G} =
    left-unit-law-comp-hom-map-precategory-Precategory {F} {G}
  pr2
    ( pr2 is-unital-composition-operation-map-precategory-Precategory)
    { F} {G} =
    right-unit-law-comp-hom-map-precategory-Precategory {F} {G}

  map-precategory-Precategory :
    Precategory (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  pr1 map-precategory-Precategory = map-Precategory C D
  pr1 (pr2 map-precategory-Precategory) =
    natural-transformation-map-set-Precategory C D
  pr1 (pr2 (pr2 map-precategory-Precategory)) =
    associative-composition-operation-map-precategory-Precategory
  pr2 (pr2 (pr2 map-precategory-Precategory)) =
    is-unital-composition-operation-map-precategory-Precategory
```

## Properties

### Isomorphisms in the map precategory are natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  where

  is-iso-map-is-natural-isomorphism-map-Precategory :
    (f : natural-transformation-map-Precategory C D F G) →
    is-natural-isomorphism-map-Precategory C D F G f →
    is-iso-Precategory (map-precategory-Precategory C D) {F} {G} f
  pr1 (is-iso-map-is-natural-isomorphism-map-Precategory f is-iso-f) =
    natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
      C D F G f is-iso-f
  pr1 (pr2 (is-iso-map-is-natural-isomorphism-map-Precategory f is-iso-f)) =
    is-section-natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
      C D F G f is-iso-f
  pr2 (pr2 (is-iso-map-is-natural-isomorphism-map-Precategory f is-iso-f)) =
    is-retraction-natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
      C D F G f is-iso-f

  is-natural-isomorphism-map-is-iso-map-Precategory :
    (f : natural-transformation-map-Precategory C D F G) →
    is-iso-Precategory (map-precategory-Precategory C D) {F} {G} f →
    is-natural-isomorphism-map-Precategory C D F G f
  pr1 (is-natural-isomorphism-map-is-iso-map-Precategory f is-iso-f x) =
    hom-family-natural-transformation-map-Precategory C D G F
      ( hom-inv-is-iso-Precategory
        ( map-precategory-Precategory C D) {F} {G} is-iso-f)
      ( x)
  pr1 (pr2 (is-natural-isomorphism-map-is-iso-map-Precategory f is-iso-f x)) =
    htpy-eq
      ( ap
        ( hom-family-natural-transformation-map-Precategory C D G G)
        ( is-section-hom-inv-is-iso-Precategory
          ( map-precategory-Precategory C D) {F} {G} is-iso-f))
      ( x)
  pr2 (pr2 (is-natural-isomorphism-map-is-iso-map-Precategory f is-iso-f x)) =
    htpy-eq
      ( ap
        ( hom-family-natural-transformation-map-Precategory C D F F)
        ( is-retraction-hom-inv-is-iso-Precategory
          ( map-precategory-Precategory C D) {F} {G} is-iso-f))
      ( x)

  is-equiv-is-iso-map-is-natural-isomorphism-map-Precategory :
    (f : natural-transformation-map-Precategory C D F G) →
    is-equiv (is-iso-map-is-natural-isomorphism-map-Precategory f)
  is-equiv-is-iso-map-is-natural-isomorphism-map-Precategory f =
    is-equiv-has-converse-is-prop
      ( is-prop-is-natural-isomorphism-map-Precategory C D F G f)
      ( is-prop-is-iso-Precategory
        ( map-precategory-Precategory C D) {F} {G} f)
      ( is-natural-isomorphism-map-is-iso-map-Precategory f)

  is-equiv-is-natural-isomorphism-map-is-iso-map-Precategory :
    (f : natural-transformation-map-Precategory C D F G) →
    is-equiv (is-natural-isomorphism-map-is-iso-map-Precategory f)
  is-equiv-is-natural-isomorphism-map-is-iso-map-Precategory f =
    is-equiv-has-converse-is-prop
      ( is-prop-is-iso-Precategory
        ( map-precategory-Precategory C D) {F} {G} f)
      ( is-prop-is-natural-isomorphism-map-Precategory C D F G f)
      ( is-iso-map-is-natural-isomorphism-map-Precategory f)

  equiv-is-iso-map-is-natural-isomorphism-map-Precategory :
    (f : natural-transformation-map-Precategory C D F G) →
    is-natural-isomorphism-map-Precategory C D F G f ≃
    is-iso-Precategory (map-precategory-Precategory C D) {F} {G} f
  pr1 (equiv-is-iso-map-is-natural-isomorphism-map-Precategory f) =
    is-iso-map-is-natural-isomorphism-map-Precategory f
  pr2 (equiv-is-iso-map-is-natural-isomorphism-map-Precategory f) =
    is-equiv-is-iso-map-is-natural-isomorphism-map-Precategory f

  equiv-is-natural-isomorphism-map-is-iso-map-Precategory :
    (f : natural-transformation-map-Precategory C D F G) →
    is-iso-Precategory (map-precategory-Precategory C D) {F} {G} f ≃
    is-natural-isomorphism-map-Precategory C D F G f
  pr1 (equiv-is-natural-isomorphism-map-is-iso-map-Precategory f) =
    is-natural-isomorphism-map-is-iso-map-Precategory f
  pr2 (equiv-is-natural-isomorphism-map-is-iso-map-Precategory f) =
    is-equiv-is-natural-isomorphism-map-is-iso-map-Precategory f

  iso-map-natural-isomorphism-map-Precategory :
    natural-isomorphism-map-Precategory C D F G →
    iso-Precategory (map-precategory-Precategory C D) F G
  iso-map-natural-isomorphism-map-Precategory =
    tot is-iso-map-is-natural-isomorphism-map-Precategory

  natural-isomorphism-map-iso-map-Precategory :
    iso-Precategory (map-precategory-Precategory C D) F G →
    natural-isomorphism-map-Precategory C D F G
  natural-isomorphism-map-iso-map-Precategory =
    tot is-natural-isomorphism-map-is-iso-map-Precategory

  is-equiv-iso-map-natural-isomorphism-map-Precategory :
    is-equiv iso-map-natural-isomorphism-map-Precategory
  is-equiv-iso-map-natural-isomorphism-map-Precategory =
    is-equiv-tot-is-fiberwise-equiv
      is-equiv-is-iso-map-is-natural-isomorphism-map-Precategory

  is-equiv-natural-isomorphism-map-iso-map-Precategory :
    is-equiv natural-isomorphism-map-iso-map-Precategory
  is-equiv-natural-isomorphism-map-iso-map-Precategory =
    is-equiv-tot-is-fiberwise-equiv
      is-equiv-is-natural-isomorphism-map-is-iso-map-Precategory

  equiv-iso-map-natural-isomorphism-map-Precategory :
    natural-isomorphism-map-Precategory C D F G ≃
    iso-Precategory (map-precategory-Precategory C D) F G
  equiv-iso-map-natural-isomorphism-map-Precategory =
    equiv-tot equiv-is-iso-map-is-natural-isomorphism-map-Precategory

  equiv-natural-isomorphism-map-iso-map-Precategory :
    iso-Precategory (map-precategory-Precategory C D) F G ≃
    natural-isomorphism-map-Precategory C D F G
  equiv-natural-isomorphism-map-iso-map-Precategory =
    equiv-tot equiv-is-natural-isomorphism-map-is-iso-map-Precategory
```

#### Computing with the equivalence that isomorphisms are natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  where

  compute-iso-map-natural-isomorphism-map-eq-Precategory :
    (p : F ＝ G) →
    iso-eq-Precategory (map-precategory-Precategory C D) F G p ＝
    iso-map-natural-isomorphism-map-Precategory C D F G
      ( natural-isomorphism-map-eq-Precategory C D F G p)
  compute-iso-map-natural-isomorphism-map-eq-Precategory refl =
    eq-iso-eq-hom-Precategory (map-precategory-Precategory C D) _ _ refl
```
