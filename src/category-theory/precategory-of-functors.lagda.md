# The precategory of functors and natural transformations between two precategories

```agda
module category-theory.precategory-of-functors where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.natural-isomorphisms-functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels
```

</details>

## Idea

[Functors](category-theory.functors-precategories.md) between
[precategories](category-theory.precategories.md) and
[natural transformations](category-theory.natural-transformations-functors-precategories.md)
between them introduce a new precategory whose identity map and composition
structure are inherited pointwise from the codomain precategory. This is called
the **precategory of functors**.

## Definitions

### The precategory of functors and natural transformations between precategories

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  comp-hom-functor-precategory-Precategory :
    {F G H : functor-Precategory C D} →
    natural-transformation-Precategory C D G H →
    natural-transformation-Precategory C D F G →
    natural-transformation-Precategory C D F H
  comp-hom-functor-precategory-Precategory {F} {G} {H} =
    comp-natural-transformation-Precategory C D F G H

  associative-comp-hom-functor-precategory-Precategory :
    {F G H I : functor-Precategory C D}
    (h : natural-transformation-Precategory C D H I)
    (g : natural-transformation-Precategory C D G H)
    (f : natural-transformation-Precategory C D F G) →
    comp-natural-transformation-Precategory C D F G I
      ( comp-natural-transformation-Precategory C D G H I h g)
      ( f) ＝
    comp-natural-transformation-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-Precategory C D F G H g f)
  associative-comp-hom-functor-precategory-Precategory {F} {G} {H} {I} h g f =
    associative-comp-natural-transformation-Precategory
      C D F G H I f g h

  involutive-eq-associative-comp-hom-functor-precategory-Precategory :
    {F G H I : functor-Precategory C D}
    (h : natural-transformation-Precategory C D H I)
    (g : natural-transformation-Precategory C D G H)
    (f : natural-transformation-Precategory C D F G) →
    comp-natural-transformation-Precategory C D F G I
      ( comp-natural-transformation-Precategory C D G H I h g)
      ( f) ＝ⁱ
    comp-natural-transformation-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-Precategory C D F G H g f)
  involutive-eq-associative-comp-hom-functor-precategory-Precategory
    { F} {G} {H} {I} h g f =
    involutive-eq-associative-comp-natural-transformation-Precategory
      C D F G H I f g h

  associative-composition-operation-functor-precategory-Precategory :
    associative-composition-operation-binary-family-Set
      ( natural-transformation-set-Precategory C D)
  pr1 associative-composition-operation-functor-precategory-Precategory
    {F} {G} {H} =
    comp-hom-functor-precategory-Precategory {F} {G} {H}
  pr2
    associative-composition-operation-functor-precategory-Precategory
      { F} {G} {H} {I} h g f =
    involutive-eq-associative-comp-hom-functor-precategory-Precategory
      { F} {G} {H} {I} h g f

  id-hom-functor-precategory-Precategory :
    (F : functor-Precategory C D) → natural-transformation-Precategory C D F F
  id-hom-functor-precategory-Precategory =
    id-natural-transformation-Precategory C D

  left-unit-law-comp-hom-functor-precategory-Precategory :
    {F G : functor-Precategory C D}
    (α : natural-transformation-Precategory C D F G) →
    comp-natural-transformation-Precategory C D F G G
      ( id-natural-transformation-Precategory C D G) α ＝
    α
  left-unit-law-comp-hom-functor-precategory-Precategory {F} {G} =
    left-unit-law-comp-natural-transformation-Precategory C D F G

  right-unit-law-comp-hom-functor-precategory-Precategory :
    {F G : functor-Precategory C D}
    (α : natural-transformation-Precategory C D F G) →
    comp-natural-transformation-Precategory C D F F G
        α (id-natural-transformation-Precategory C D F) ＝
    α
  right-unit-law-comp-hom-functor-precategory-Precategory {F} {G} =
    right-unit-law-comp-natural-transformation-Precategory C D F G

  is-unital-composition-operation-functor-precategory-Precategory :
    is-unital-composition-operation-binary-family-Set
      ( natural-transformation-set-Precategory C D)
      ( λ {F} {G} {H} → comp-hom-functor-precategory-Precategory {F} {G} {H})
  pr1 is-unital-composition-operation-functor-precategory-Precategory =
    id-hom-functor-precategory-Precategory
  pr1
    ( pr2 is-unital-composition-operation-functor-precategory-Precategory)
    { F} {G} =
    left-unit-law-comp-hom-functor-precategory-Precategory {F} {G}
  pr2
    ( pr2 is-unital-composition-operation-functor-precategory-Precategory)
    { F} {G} =
    right-unit-law-comp-hom-functor-precategory-Precategory {F} {G}

  functor-precategory-Precategory :
    Precategory (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  pr1 functor-precategory-Precategory = functor-Precategory C D
  pr1 (pr2 functor-precategory-Precategory) =
    natural-transformation-set-Precategory C D
  pr1 (pr2 (pr2 functor-precategory-Precategory)) =
    associative-composition-operation-functor-precategory-Precategory
  pr2 (pr2 (pr2 functor-precategory-Precategory)) =
    is-unital-composition-operation-functor-precategory-Precategory
```

## Properties

### Isomorphisms in the functor precategory are natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  is-iso-functor-is-natural-isomorphism-Precategory :
    (f : natural-transformation-Precategory C D F G) →
    is-natural-isomorphism-Precategory C D F G f →
    is-iso-Precategory (functor-precategory-Precategory C D) {F} {G} f
  pr1 (is-iso-functor-is-natural-isomorphism-Precategory f is-iso-f) =
    natural-transformation-inv-is-natural-isomorphism-Precategory
      C D F G f is-iso-f
  pr1 (pr2 (is-iso-functor-is-natural-isomorphism-Precategory f is-iso-f)) =
    is-section-natural-transformation-inv-is-natural-isomorphism-Precategory
      C D F G f is-iso-f
  pr2 (pr2 (is-iso-functor-is-natural-isomorphism-Precategory f is-iso-f)) =
    is-retraction-natural-transformation-inv-is-natural-isomorphism-Precategory
      C D F G f is-iso-f

  is-natural-isomorphism-is-iso-functor-Precategory :
    (f : natural-transformation-Precategory C D F G) →
    is-iso-Precategory (functor-precategory-Precategory C D) {F} {G} f →
    is-natural-isomorphism-Precategory C D F G f
  pr1 (is-natural-isomorphism-is-iso-functor-Precategory f is-iso-f x) =
    hom-family-natural-transformation-Precategory C D G F
      ( hom-inv-is-iso-Precategory
        ( functor-precategory-Precategory C D) {F} {G} is-iso-f)
      ( x)
  pr1 (pr2 (is-natural-isomorphism-is-iso-functor-Precategory f is-iso-f x)) =
    htpy-eq
      ( ap
        ( hom-family-natural-transformation-Precategory C D G G)
        ( is-section-hom-inv-is-iso-Precategory
          ( functor-precategory-Precategory C D) {F} {G} is-iso-f))
      ( x)
  pr2 (pr2 (is-natural-isomorphism-is-iso-functor-Precategory f is-iso-f x)) =
    htpy-eq
      ( ap
        ( hom-family-natural-transformation-Precategory C D F F)
        ( is-retraction-hom-inv-is-iso-Precategory
          ( functor-precategory-Precategory C D) {F} {G} is-iso-f))
      ( x)

  is-equiv-is-iso-functor-is-natural-isomorphism-Precategory :
    (f : natural-transformation-Precategory C D F G) →
    is-equiv (is-iso-functor-is-natural-isomorphism-Precategory f)
  is-equiv-is-iso-functor-is-natural-isomorphism-Precategory f =
    is-equiv-has-converse-is-prop
      ( is-prop-is-natural-isomorphism-Precategory C D F G f)
      ( is-prop-is-iso-Precategory
        ( functor-precategory-Precategory C D) {F} {G} f)
      ( is-natural-isomorphism-is-iso-functor-Precategory f)

  is-equiv-is-natural-isomorphism-is-iso-functor-Precategory :
    (f : natural-transformation-Precategory C D F G) →
    is-equiv (is-natural-isomorphism-is-iso-functor-Precategory f)
  is-equiv-is-natural-isomorphism-is-iso-functor-Precategory f =
    is-equiv-has-converse-is-prop
      ( is-prop-is-iso-Precategory
        ( functor-precategory-Precategory C D) {F} {G} f)
      ( is-prop-is-natural-isomorphism-Precategory C D F G f)
      ( is-iso-functor-is-natural-isomorphism-Precategory f)

  equiv-is-iso-functor-is-natural-isomorphism-Precategory :
    (f : natural-transformation-Precategory C D F G) →
    is-natural-isomorphism-Precategory C D F G f ≃
    is-iso-Precategory (functor-precategory-Precategory C D) {F} {G} f
  pr1 (equiv-is-iso-functor-is-natural-isomorphism-Precategory f) =
    is-iso-functor-is-natural-isomorphism-Precategory f
  pr2 (equiv-is-iso-functor-is-natural-isomorphism-Precategory f) =
    is-equiv-is-iso-functor-is-natural-isomorphism-Precategory f

  equiv-is-natural-isomorphism-is-iso-functor-Precategory :
    (f : natural-transformation-Precategory C D F G) →
    is-iso-Precategory (functor-precategory-Precategory C D) {F} {G} f ≃
    is-natural-isomorphism-Precategory C D F G f
  pr1 (equiv-is-natural-isomorphism-is-iso-functor-Precategory f) =
    is-natural-isomorphism-is-iso-functor-Precategory f
  pr2 (equiv-is-natural-isomorphism-is-iso-functor-Precategory f) =
    is-equiv-is-natural-isomorphism-is-iso-functor-Precategory f

  iso-functor-natural-isomorphism-Precategory :
    natural-isomorphism-Precategory C D F G →
    iso-Precategory (functor-precategory-Precategory C D) F G
  iso-functor-natural-isomorphism-Precategory =
    tot is-iso-functor-is-natural-isomorphism-Precategory

  natural-isomorphism-iso-functor-Precategory :
    iso-Precategory (functor-precategory-Precategory C D) F G →
    natural-isomorphism-Precategory C D F G
  natural-isomorphism-iso-functor-Precategory =
    tot is-natural-isomorphism-is-iso-functor-Precategory

  is-equiv-iso-functor-natural-isomorphism-Precategory :
    is-equiv iso-functor-natural-isomorphism-Precategory
  is-equiv-iso-functor-natural-isomorphism-Precategory =
    is-equiv-tot-is-fiberwise-equiv
      is-equiv-is-iso-functor-is-natural-isomorphism-Precategory

  is-equiv-natural-isomorphism-iso-functor-Precategory :
    is-equiv natural-isomorphism-iso-functor-Precategory
  is-equiv-natural-isomorphism-iso-functor-Precategory =
    is-equiv-tot-is-fiberwise-equiv
      is-equiv-is-natural-isomorphism-is-iso-functor-Precategory

  equiv-iso-functor-natural-isomorphism-Precategory :
    natural-isomorphism-Precategory C D F G ≃
    iso-Precategory (functor-precategory-Precategory C D) F G
  equiv-iso-functor-natural-isomorphism-Precategory =
    equiv-tot equiv-is-iso-functor-is-natural-isomorphism-Precategory

  equiv-natural-isomorphism-iso-functor-Precategory :
    iso-Precategory (functor-precategory-Precategory C D) F G ≃
    natural-isomorphism-Precategory C D F G
  equiv-natural-isomorphism-iso-functor-Precategory =
    equiv-tot equiv-is-natural-isomorphism-is-iso-functor-Precategory
```

#### Computing with the equivalence that isomorphisms are natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  compute-iso-functor-natural-isomorphism-eq-Precategory :
    (p : F ＝ G) →
    iso-eq-Precategory (functor-precategory-Precategory C D) F G p ＝
    iso-functor-natural-isomorphism-Precategory C D F G
      ( natural-isomorphism-eq-Precategory C D F G p)
  compute-iso-functor-natural-isomorphism-eq-Precategory refl =
    eq-iso-eq-hom-Precategory
      ( functor-precategory-Precategory C D)
      { F} {G} _ _ refl
```

### The evaluation functor

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  ev-functor-Precategory :
    (c : obj-Precategory C) →
    functor-Precategory (functor-precategory-Precategory C D) D
  pr1 (ev-functor-Precategory c) F = obj-functor-Precategory C D F c
  pr1 (pr2 (ev-functor-Precategory c)) {F} {G} φ =
    hom-family-natural-transformation-Precategory C D F G φ c
  pr1 (pr2 (pr2 (ev-functor-Precategory c))) φ Ψ = refl
  pr2 (pr2 (pr2 (ev-functor-Precategory c))) F = refl
```
