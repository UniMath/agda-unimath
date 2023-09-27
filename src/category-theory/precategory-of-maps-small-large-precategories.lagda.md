# The precategory of maps and natural transformations from a small to a large precategory

```agda
module category-theory.precategory-of-maps-small-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-small-large-precategories
open import category-theory.maps-precategories
open import category-theory.large-precategories
open import category-theory.natural-isomorphisms-maps-precategories
open import category-theory.natural-transformations-maps-small-large-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

[Maps](category-theory.maps-small-large-precategories.md) from
[(small) precategories](category-theory.precategories.md) to
[large precategories](category-theory.large-precategories.md) and
[natural transformations](category-theory.natural-transformations-maps-precategories.md)
between them introduce a new large precategory whose identity map and
composition structure are inherited pointwise from the codomain precategory.
This is called the **precategory of maps from a small to a large precategory**.

## Definitions

### The large precategory of maps and natural transformations from a small to a large precategory

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2) (D : Large-Precategory α β)
  where

  comp-hom-map-large-precategory-Small-Large-Precategory :
    {γF γG γH : Level}
    {F : map-Small-Large-Precategory C D γF}
    {G : map-Small-Large-Precategory C D γG}
    {H : map-Small-Large-Precategory C D γH} →
    natural-transformation-map-Small-Large-Precategory C D G H →
    natural-transformation-map-Small-Large-Precategory C D F G →
    natural-transformation-map-Small-Large-Precategory C D F H
  comp-hom-map-large-precategory-Small-Large-Precategory {F = F} {G} {H} =
    comp-natural-transformation-map-Small-Large-Precategory C D F G H

  associative-comp-hom-map-large-precategory-Small-Large-Precategory :
    {γF γG γH γI : Level}
    {F : map-Small-Large-Precategory C D γF}
    {G : map-Small-Large-Precategory C D γG}
    {H : map-Small-Large-Precategory C D γH}
    {I : map-Small-Large-Precategory C D γI}
    (h : natural-transformation-map-Small-Large-Precategory C D H I)
    (g : natural-transformation-map-Small-Large-Precategory C D G H)
    (f : natural-transformation-map-Small-Large-Precategory C D F G) →
    ( comp-natural-transformation-map-Small-Large-Precategory C D F G I
      ( comp-natural-transformation-map-Small-Large-Precategory C D G H I h g)
      ( f)) ＝
    ( comp-natural-transformation-map-Small-Large-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-map-Small-Large-Precategory C D F G H g f))
  associative-comp-hom-map-large-precategory-Small-Large-Precategory
    {F = F} {G} {H} {I} h g f =
    associative-comp-natural-transformation-map-Small-Large-Precategory
      C D F G H I f g h

  id-hom-map-large-precategory-Small-Large-Precategory :
    {γF : Level} {F : map-Small-Large-Precategory C D γF} →
    natural-transformation-map-Small-Large-Precategory C D F F
  id-hom-map-large-precategory-Small-Large-Precategory {F = F} =
    id-natural-transformation-map-Small-Large-Precategory C D F

  left-unit-law-comp-hom-map-large-precategory-Small-Large-Precategory :
    {γF γG : Level}
    {F : map-Small-Large-Precategory C D γF}
    {G : map-Small-Large-Precategory C D γG}
    (a : natural-transformation-map-Small-Large-Precategory C D F G) →
    ( comp-natural-transformation-map-Small-Large-Precategory C D F G G
      ( id-natural-transformation-map-Small-Large-Precategory C D G) a) ＝
    ( a)
  left-unit-law-comp-hom-map-large-precategory-Small-Large-Precategory
    { F = F} {G} =
    left-unit-law-comp-natural-transformation-map-Small-Large-Precategory
      C D F G

  right-unit-law-comp-hom-map-large-precategory-Small-Large-Precategory :
    {γF γG : Level}
    {F : map-Small-Large-Precategory C D γF}
    {G : map-Small-Large-Precategory C D γG}
    (a : natural-transformation-map-Small-Large-Precategory C D F G) →
    ( comp-natural-transformation-map-Small-Large-Precategory C D F F G
        a (id-natural-transformation-map-Small-Large-Precategory C D F)) ＝
    ( a)
  right-unit-law-comp-hom-map-large-precategory-Small-Large-Precategory
    { F = F} {G} =
    right-unit-law-comp-natural-transformation-map-Small-Large-Precategory
      C D F G

  map-large-precategory-Small-Large-Precategory :
    Large-Precategory (λ l → l1 ⊔ l2 ⊔ α l ⊔ β l l) (λ l l' → l1 ⊔ l2 ⊔ β l l')
  obj-Large-Precategory map-large-precategory-Small-Large-Precategory =
    map-Small-Large-Precategory C D
  hom-set-Large-Precategory map-large-precategory-Small-Large-Precategory =
    natural-transformation-map-set-Small-Large-Precategory C D
  comp-hom-Large-Precategory map-large-precategory-Small-Large-Precategory =
    comp-hom-map-large-precategory-Small-Large-Precategory
  id-hom-Large-Precategory map-large-precategory-Small-Large-Precategory =
    id-hom-map-large-precategory-Small-Large-Precategory
  associative-comp-hom-Large-Precategory map-large-precategory-Small-Large-Precategory =
    associative-comp-hom-map-large-precategory-Small-Large-Precategory
  left-unit-law-comp-hom-Large-Precategory map-large-precategory-Small-Large-Precategory =
    left-unit-law-comp-hom-map-large-precategory-Small-Large-Precategory
  right-unit-law-comp-hom-Large-Precategory map-large-precategory-Small-Large-Precategory =
    right-unit-law-comp-hom-map-large-precategory-Small-Large-Precategory
```

### The small precategories of maps and natural transformations from a small to a large precategory

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2) (D : Large-Precategory α β)
  where

  map-precategory-Small-Large-Precategory :
    (l : Level) → Precategory (l1 ⊔ l2 ⊔ α l ⊔ β l l) (l1 ⊔ l2 ⊔ β l l)
  map-precategory-Small-Large-Precategory =
    precategory-Large-Precategory
      ( map-large-precategory-Small-Large-Precategory C D)
```

## Properties

### Isomorphisms in the map precategory are natural isomorphisms

```agda
-- module _
--   {l1 l2 l3 l4 : Level}
--   (C : Precategory l1 l2)
--   (D : Precategory l3 l4)
--   (F G : map-Small-Large-Precategory C D)
--   where

--   is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory :
--     (f : natural-transformation-map-Small-Large-Precategory C D F G) →
--     is-natural-isomorphism-map-Small-Large-Precategory C D F G f →
--     is-iso-Precategory (map-large-precategory-Small-Large-Precategory C D) {F} {G} f
--   pr1 (is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory f is-iso-f) =
--     natural-transformation-map-inv-is-natural-isomorphism-map-Small-Large-Precategory
--       C D F G f is-iso-f
--   pr1 (pr2 (is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory f is-iso-f)) =
--     is-section-natural-transformation-map-inv-is-natural-isomorphism-map-Small-Large-Precategory
--       C D F G f is-iso-f
--   pr2 (pr2 (is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory f is-iso-f)) =
--     is-retraction-natural-transformation-map-inv-is-natural-isomorphism-map-Small-Large-Precategory
--       C D F G f is-iso-f

--   is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory :
--     (f : natural-transformation-map-Small-Large-Precategory C D F G) →
--     is-iso-Precategory (map-large-precategory-Small-Large-Precategory C D) {F} {G} f →
--     is-natural-isomorphism-map-Small-Large-Precategory C D F G f
--   pr1 (is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory f is-iso-f x) =
--     hom-family-natural-transformation-map-Small-Large-Precategory C D G F
--       ( hom-inv-is-iso-Precategory
--         ( map-large-precategory-Small-Large-Precategory C D) {F} {G} is-iso-f)
--       ( x)
--   pr1 (pr2 (is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory f is-iso-f x)) =
--     htpy-eq
--       ( ap
--         ( hom-family-natural-transformation-map-Small-Large-Precategory C D G G)
--         ( is-section-hom-inv-is-iso-Precategory
--           ( map-large-precategory-Small-Large-Precategory C D) {F} {G} is-iso-f))
--       ( x)
--   pr2 (pr2 (is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory f is-iso-f x)) =
--     htpy-eq
--       ( ap
--         ( hom-family-natural-transformation-map-Small-Large-Precategory C D F F)
--         ( is-retraction-hom-inv-is-iso-Precategory
--           ( map-large-precategory-Small-Large-Precategory C D) {F} {G} is-iso-f))
--       ( x)

--   is-equiv-is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory :
--     (f : natural-transformation-map-Small-Large-Precategory C D F G) →
--     is-equiv (is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory f)
--   is-equiv-is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory f =
--     is-equiv-is-prop
--       ( is-prop-is-natural-isomorphism-map-Small-Large-Precategory C D F G f)
--       ( is-prop-is-iso-Precategory
--         ( map-large-precategory-Small-Large-Precategory C D) {F} {G} f)
--       ( is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory f)

--   is-equiv-is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory :
--     (f : natural-transformation-map-Small-Large-Precategory C D F G) →
--     is-equiv (is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory f)
--   is-equiv-is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory f =
--     is-equiv-is-prop
--       ( is-prop-is-iso-Precategory
--         ( map-large-precategory-Small-Large-Precategory C D) {F} {G} f)
--       ( is-prop-is-natural-isomorphism-map-Small-Large-Precategory C D F G f)
--       ( is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory f)

--   equiv-is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory :
--     (f : natural-transformation-map-Small-Large-Precategory C D F G) →
--     is-natural-isomorphism-map-Small-Large-Precategory C D F G f ≃
--     is-iso-Precategory (map-large-precategory-Small-Large-Precategory C D) {F} {G} f
--   pr1 (equiv-is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory f) =
--     is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory f
--   pr2 (equiv-is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory f) =
--     is-equiv-is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory f

--   equiv-is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory :
--     (f : natural-transformation-map-Small-Large-Precategory C D F G) →
--     is-iso-Precategory (map-large-precategory-Small-Large-Precategory C D) {F} {G} f ≃
--     is-natural-isomorphism-map-Small-Large-Precategory C D F G f
--   pr1 (equiv-is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory f) =
--     is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory f
--   pr2 (equiv-is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory f) =
--     is-equiv-is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory f

--   iso-map-natural-isomorphism-map-Small-Large-Precategory :
--     natural-isomorphism-map-Small-Large-Precategory C D F G →
--     iso-Precategory (map-large-precategory-Small-Large-Precategory C D) F G
--   iso-map-natural-isomorphism-map-Small-Large-Precategory =
--     tot is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory

--   natural-isomorphism-map-iso-map-Small-Large-Precategory :
--     iso-Precategory (map-large-precategory-Small-Large-Precategory C D) F G →
--     natural-isomorphism-map-Small-Large-Precategory C D F G
--   natural-isomorphism-map-iso-map-Small-Large-Precategory =
--     tot is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory

--   is-equiv-iso-map-natural-isomorphism-map-Small-Large-Precategory :
--     is-equiv iso-map-natural-isomorphism-map-Small-Large-Precategory
--   is-equiv-iso-map-natural-isomorphism-map-Small-Large-Precategory =
--     is-equiv-tot-is-fiberwise-equiv
--       is-equiv-is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory

--   is-equiv-natural-isomorphism-map-iso-map-Small-Large-Precategory :
--     is-equiv natural-isomorphism-map-iso-map-Small-Large-Precategory
--   is-equiv-natural-isomorphism-map-iso-map-Small-Large-Precategory =
--     is-equiv-tot-is-fiberwise-equiv
--       is-equiv-is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory

--   equiv-iso-map-natural-isomorphism-map-Small-Large-Precategory :
--     natural-isomorphism-map-Small-Large-Precategory C D F G ≃
--     iso-Precategory (map-large-precategory-Small-Large-Precategory C D) F G
--   equiv-iso-map-natural-isomorphism-map-Small-Large-Precategory =
--     equiv-tot equiv-is-iso-map-is-natural-isomorphism-map-Small-Large-Precategory

--   equiv-natural-isomorphism-map-iso-map-Small-Large-Precategory :
--     iso-Precategory (map-large-precategory-Small-Large-Precategory C D) F G ≃
--     natural-isomorphism-map-Small-Large-Precategory C D F G
--   equiv-natural-isomorphism-map-iso-map-Small-Large-Precategory =
--     equiv-tot equiv-is-natural-isomorphism-map-is-iso-map-Small-Large-Precategory
```

#### Computing with the equivalence that isomorphisms are natural isomorphisms

```agda
-- module _
--   {l1 l2 l3 l4 : Level}
--   (C : Precategory l1 l2)
--   (D : Precategory l3 l4)
--   (F G : map-Small-Large-Precategory C D)
--   where

--   compute-iso-map-natural-isomorphism-map-eq-Precategory :
--     (p : F ＝ G) →
--     iso-eq-Precategory (map-large-precategory-Small-Large-Precategory C D) F G p ＝
--     iso-map-natural-isomorphism-map-Small-Large-Precategory C D F G
--       ( natural-isomorphism-map-eq-Precategory C D F G p)
--   compute-iso-map-natural-isomorphism-map-eq-Precategory refl =
--     eq-iso-eq-hom-Precategory (map-large-precategory-Small-Large-Precategory C D) _ _ refl
```
