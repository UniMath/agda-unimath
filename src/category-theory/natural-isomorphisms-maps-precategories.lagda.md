# Natural isomorphisms between maps between precategories

```agda
module category-theory.natural-isomorphisms-maps-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **natural isomorphism** `γ` from [map](category-theory.maps-precategories.md)
`F : C → D` to `G : C → D` is a
[natural transformation](category-theory.natural-transformations-maps-precategories.md)
from `F` to `G` such that the morphism `γ F : hom (F x) (G x)` is an
[isomorphism](category-theory.isomorphisms-in-precategories.md), for every
object `x` in `C`.

## Definition

### Families of isomorphisms between maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  where

  iso-family-map-Precategory : UU (l1 ⊔ l4)
  iso-family-map-Precategory =
    (x : obj-Precategory C) →
    iso-Precategory D
      ( obj-map-Precategory C D F x)
      ( obj-map-Precategory C D G x)
```

### The predicate of being an isomorphism in a precategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  where

  is-natural-isomorphism-map-Precategory :
    natural-transformation-map-Precategory C D F G → UU (l1 ⊔ l4)
  is-natural-isomorphism-map-Precategory f =
    (x : obj-Precategory C) →
    is-iso-Precategory D
      ( hom-family-natural-transformation-map-Precategory C D F G f x)

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  (f : natural-transformation-map-Precategory C D F G)
  where

  hom-inv-family-is-natural-isomorphism-map-Precategory :
    is-natural-isomorphism-map-Precategory C D F G f →
    hom-family-map-Precategory C D G F
  hom-inv-family-is-natural-isomorphism-map-Precategory is-iso-f =
    hom-inv-is-iso-Precategory D ∘ is-iso-f

  is-section-hom-inv-family-is-natural-isomorphism-map-Precategory :
    (is-iso-f : is-natural-isomorphism-map-Precategory C D F G f) →
    (x : obj-Precategory C) →
    comp-hom-Precategory D
      ( hom-family-natural-transformation-map-Precategory C D F G f x)
      ( hom-inv-is-iso-Precategory D (is-iso-f x)) ＝
    id-hom-Precategory D
  is-section-hom-inv-family-is-natural-isomorphism-map-Precategory is-iso-f =
    is-section-hom-inv-is-iso-Precategory D ∘ is-iso-f

  is-retraction-hom-inv-family-is-natural-isomorphism-map-Precategory :
    (is-iso-f : is-natural-isomorphism-map-Precategory C D F G f) →
    (x : obj-Precategory C) →
    comp-hom-Precategory D
      ( hom-inv-is-iso-Precategory D (is-iso-f x))
      ( hom-family-natural-transformation-map-Precategory C D F G f x) ＝
    id-hom-Precategory D
  is-retraction-hom-inv-family-is-natural-isomorphism-map-Precategory is-iso-f =
    is-retraction-hom-inv-is-iso-Precategory D ∘ is-iso-f

  iso-family-is-natural-isomorphism-map-Precategory :
    is-natural-isomorphism-map-Precategory C D F G f →
    iso-family-map-Precategory C D F G
  pr1 (iso-family-is-natural-isomorphism-map-Precategory is-iso-f x) =
    hom-family-natural-transformation-map-Precategory C D F G f x
  pr2 (iso-family-is-natural-isomorphism-map-Precategory is-iso-f x) =
    is-iso-f x

  inv-iso-family-is-natural-isomorphism-map-Precategory :
    is-natural-isomorphism-map-Precategory C D F G f →
    iso-family-map-Precategory C D G F
  inv-iso-family-is-natural-isomorphism-map-Precategory is-iso-f =
    inv-iso-Precategory D ∘
    iso-family-is-natural-isomorphism-map-Precategory is-iso-f
```

### Natural isomorphisms in a precategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  where

  natural-isomorphism-map-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  natural-isomorphism-map-Precategory =
    Σ ( natural-transformation-map-Precategory C D F G)
      ( is-natural-isomorphism-map-Precategory C D F G)

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  (f : natural-isomorphism-map-Precategory C D F G)
  where

  natural-transformation-map-natural-isomorphism-map-Precategory :
    natural-transformation-map-Precategory C D F G
  natural-transformation-map-natural-isomorphism-map-Precategory = pr1 f

  hom-family-natural-isomorphism-map-Precategory :
    hom-family-map-Precategory C D F G
  hom-family-natural-isomorphism-map-Precategory =
    hom-family-natural-transformation-map-Precategory C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory)

  coherence-square-natural-isomorphism-map-Precategory :
    is-natural-transformation-map-Precategory C D F G
      ( hom-family-natural-transformation-map-Precategory C D F G
        ( natural-transformation-map-natural-isomorphism-map-Precategory))
  coherence-square-natural-isomorphism-map-Precategory =
    naturality-natural-transformation-map-Precategory C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory)

  is-natural-isomorphism-map-natural-isomorphism-map-Precategory :
    is-natural-isomorphism-map-Precategory C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory)
  is-natural-isomorphism-map-natural-isomorphism-map-Precategory = pr2 f

  hom-inv-family-natural-isomorphism-map-Precategory :
    hom-family-map-Precategory C D G F
  hom-inv-family-natural-isomorphism-map-Precategory =
    hom-inv-family-is-natural-isomorphism-map-Precategory C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategory)

  is-section-hom-inv-family-natural-isomorphism-map-Precategory :
    (x : obj-Precategory C) →
    comp-hom-Precategory D
      ( hom-family-natural-isomorphism-map-Precategory x)
      ( hom-inv-family-natural-isomorphism-map-Precategory x) ＝
    id-hom-Precategory D
  is-section-hom-inv-family-natural-isomorphism-map-Precategory =
    is-section-hom-inv-family-is-natural-isomorphism-map-Precategory C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategory)

  is-retraction-hom-inv-family-natural-isomorphism-map-Precategory :
    (x : obj-Precategory C) →
    comp-hom-Precategory D
      ( hom-inv-family-natural-isomorphism-map-Precategory x)
      ( hom-family-natural-isomorphism-map-Precategory x) ＝
    id-hom-Precategory D
  is-retraction-hom-inv-family-natural-isomorphism-map-Precategory =
    is-retraction-hom-inv-family-is-natural-isomorphism-map-Precategory C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategory)

  iso-family-natural-isomorphism-map-Precategory :
    iso-family-map-Precategory C D F G
  iso-family-natural-isomorphism-map-Precategory =
    iso-family-is-natural-isomorphism-map-Precategory C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategory)

  inv-iso-family-natural-isomorphism-map-Precategory :
    iso-family-map-Precategory C D G F
  inv-iso-family-natural-isomorphism-map-Precategory =
    inv-iso-family-is-natural-isomorphism-map-Precategory C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategory)
```

## Examples

### The identity natural isomorphism

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  id-natural-isomorphism-map-Precategory :
    (F : map-Precategory C D) → natural-isomorphism-map-Precategory C D F F
  pr1 (id-natural-isomorphism-map-Precategory F) =
    id-natural-transformation-map-Precategory C D F
  pr2 (id-natural-isomorphism-map-Precategory F) x =
    is-iso-id-hom-Precategory D
```

### Equalities induce natural isomorphisms

An equality between maps `F` and `G` gives rise to a natural isomorphism between
them. This is because, by the J-rule, it is enough to construct a natural
isomorphism given `refl : F ＝ F`, from `F` to itself. We take the identity
natural transformation as such an isomorphism.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  natural-isomorphism-map-eq-Precategory :
    (F G : map-Precategory C D) →
    F ＝ G → natural-isomorphism-map-Precategory C D F G
  natural-isomorphism-map-eq-Precategory F .F refl =
    id-natural-isomorphism-map-Precategory C D F
```

## Propositions

### Being a natural isomorphism is a proposition

That a natural transformation is a natural isomorphism is a proposition. This
follows from the fact that being an isomorphism is a proposition.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  where

  is-prop-is-natural-isomorphism-map-Precategory :
    (f : natural-transformation-map-Precategory C D F G) →
    is-prop (is-natural-isomorphism-map-Precategory C D F G f)
  is-prop-is-natural-isomorphism-map-Precategory f =
    is-prop-Π (is-prop-is-iso-Precategory D ∘
    hom-family-natural-transformation-map-Precategory C D F G f)

  is-natural-isomorphism-map-prop-hom-Precategory :
    (f : natural-transformation-map-Precategory C D F G) → Prop (l1 ⊔ l4)
  pr1 (is-natural-isomorphism-map-prop-hom-Precategory f) =
    is-natural-isomorphism-map-Precategory C D F G f
  pr2 (is-natural-isomorphism-map-prop-hom-Precategory f) =
    is-prop-is-natural-isomorphism-map-Precategory f
```

### Equality of natural isomorphisms is equality of their underlying natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  where

  extensionality-natural-isomorphism-map-Precategory :
    (f g : natural-isomorphism-map-Precategory C D F G) →
    (f ＝ g) ≃
    ( hom-family-natural-isomorphism-map-Precategory C D F G f ~
      hom-family-natural-isomorphism-map-Precategory C D F G g)
  extensionality-natural-isomorphism-map-Precategory f g =
    ( extensionality-natural-transformation-map-Precategory C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G f)
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G g)) ∘e
    ( equiv-ap-emb
      ( emb-subtype (is-natural-isomorphism-map-prop-hom-Precategory C D F G)))

  eq-eq-natural-transformation-map-natural-isomorphism-map-Precategory :
    (f g : natural-isomorphism-map-Precategory C D F G) →
    ( ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G f) ＝
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G g)) →
    f ＝ g
  eq-eq-natural-transformation-map-natural-isomorphism-map-Precategory f g =
    eq-type-subtype (is-natural-isomorphism-map-prop-hom-Precategory C D F G)

  eq-htpy-hom-family-natural-isomorphism-map-Precategory :
        (f g : natural-isomorphism-map-Precategory C D F G) →
    ( hom-family-natural-isomorphism-map-Precategory C D F G f ~
      hom-family-natural-isomorphism-map-Precategory C D F G g) →
    f ＝ g
  eq-htpy-hom-family-natural-isomorphism-map-Precategory f g =
    eq-eq-natural-transformation-map-natural-isomorphism-map-Precategory f g ∘
    eq-htpy-hom-family-natural-transformation-map-Precategory C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G f)
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G g)
```

### The type of natural isomorphisms form a set

The type of natural isomorphisms between maps `F` and `G` is a
[subtype](foundation-core.subtypes.md) of the [set](foundation-core.sets.md)
`natural-transformation F G` since being an isomorphism is a proposition.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  where

  is-set-natural-isomorphism-map-Precategory :
    is-set (natural-isomorphism-map-Precategory C D F G)
  is-set-natural-isomorphism-map-Precategory =
    is-set-type-subtype
      ( is-natural-isomorphism-map-prop-hom-Precategory C D F G)
      ( is-set-natural-transformation-map-Precategory C D F G)

  natural-isomorphism-map-set-Precategory : Set (l1 ⊔ l2 ⊔ l4)
  pr1 natural-isomorphism-map-set-Precategory =
    natural-isomorphism-map-Precategory C D F G
  pr2 natural-isomorphism-map-set-Precategory =
    is-set-natural-isomorphism-map-Precategory
```

### Inverses of natural isomorphisms are natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  (f : natural-transformation-map-Precategory C D F G)
  where

  natural-transformation-map-inv-is-natural-isomorphism-map-Precategory :
    is-natural-isomorphism-map-Precategory C D F G f →
    natural-transformation-map-Precategory C D G F
  pr1
    ( natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
      ( is-iso-f)) =
    hom-inv-is-iso-Precategory D ∘ is-iso-f
  pr2
    ( natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
      ( is-iso-f))
    { x} {y} g =
    ( inv
      ( left-unit-law-comp-hom-Precategory D
        ( comp-hom-Precategory D
          ( hom-map-Precategory C D F g)
          ( hom-inv-family-is-natural-isomorphism-map-Precategory
              C D F G f is-iso-f x)))) ∙
    ( ap
      ( comp-hom-Precategory' D
        ( comp-hom-Precategory D
          ( hom-map-Precategory C D F g)
          ( hom-inv-family-is-natural-isomorphism-map-Precategory
              C D F G f is-iso-f x)))
      ( inv (is-retraction-hom-inv-is-iso-Precategory D (is-iso-f y)))) ∙
    ( associative-comp-hom-Precategory D
      ( hom-inv-family-is-natural-isomorphism-map-Precategory
          C D F G f is-iso-f y)
      ( hom-family-natural-transformation-map-Precategory C D F G f y)
      ( comp-hom-Precategory D
        ( hom-map-Precategory C D F g)
        ( hom-inv-family-is-natural-isomorphism-map-Precategory
            C D F G f is-iso-f x))) ∙
    ( ap
      ( comp-hom-Precategory D
        ( hom-inv-family-is-natural-isomorphism-map-Precategory
            C D F G f is-iso-f y))
      ( ( inv
          ( associative-comp-hom-Precategory D
            ( hom-family-natural-transformation-map-Precategory C D F G f y)
            ( hom-map-Precategory C D F g)
            ( hom-inv-family-is-natural-isomorphism-map-Precategory
                C D F G f is-iso-f x))) ∙
        ( ap
          ( comp-hom-Precategory' D _)
          ( inv
            ( naturality-natural-transformation-map-Precategory
                C D F G f g))) ∙
        ( associative-comp-hom-Precategory D
          ( hom-map-Precategory C D G g)
          ( hom-family-natural-transformation-map-Precategory C D F G f x)
          ( hom-inv-is-iso-Precategory D (is-iso-f x))) ∙
        ( ap
          ( comp-hom-Precategory D (hom-map-Precategory C D G g))
          ( is-section-hom-inv-is-iso-Precategory D (is-iso-f x))) ∙
        ( right-unit-law-comp-hom-Precategory D
          ( hom-map-Precategory C D G g))))

  is-section-natural-transformation-map-inv-is-natural-isomorphism-map-Precategory :
    (is-iso-f : is-natural-isomorphism-map-Precategory C D F G f) →
    comp-natural-transformation-map-Precategory C D G F G
      ( f)
      ( natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
        ( is-iso-f)) ＝
    id-natural-transformation-map-Precategory C D G
  is-section-natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
    is-iso-f =
    eq-htpy-hom-family-natural-transformation-map-Precategory C D G G _ _
      ( is-section-hom-inv-is-iso-Precategory D ∘ is-iso-f)

  is-retraction-natural-transformation-map-inv-is-natural-isomorphism-map-Precategory :
    (is-iso-f : is-natural-isomorphism-map-Precategory C D F G f) →
    comp-natural-transformation-map-Precategory C D F G F
      ( natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
        ( is-iso-f))
      ( f) ＝
    id-natural-transformation-map-Precategory C D F
  is-retraction-natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
    is-iso-f =
    eq-htpy-hom-family-natural-transformation-map-Precategory C D F F _ _
      ( is-retraction-hom-inv-is-iso-Precategory D ∘ is-iso-f)

  is-natural-isomorphism-map-inv-is-natural-isomorphism-map-Precategory :
    (is-iso-f : is-natural-isomorphism-map-Precategory C D F G f) →
    is-natural-isomorphism-map-Precategory C D G F
      ( natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
        ( is-iso-f))
  is-natural-isomorphism-map-inv-is-natural-isomorphism-map-Precategory
    is-iso-f =
    is-iso-inv-is-iso-Precategory D ∘ is-iso-f
```

### Inverses of natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  (f : natural-isomorphism-map-Precategory C D F G)
  where

  natural-transformation-map-inv-natural-isomorphism-map-Precategory :
    natural-transformation-map-Precategory C D G F
  natural-transformation-map-inv-natural-isomorphism-map-Precategory =
    natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
      C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G f)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategory
          C D F G f)

  is-section-natural-transformation-map-inv-natural-isomorphism-map-Precategory :
    ( comp-natural-transformation-map-Precategory C D G F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G f)
      ( natural-transformation-map-inv-natural-isomorphism-map-Precategory)) ＝
    ( id-natural-transformation-map-Precategory C D G)
  is-section-natural-transformation-map-inv-natural-isomorphism-map-Precategory =
    is-section-natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
      C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G f)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategory
          C D F G f)

  is-retraction-natural-transformation-map-inv-natural-isomorphism-map-Precategory :
    ( comp-natural-transformation-map-Precategory C D F G F
      ( natural-transformation-map-inv-natural-isomorphism-map-Precategory)
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G f)) ＝
    ( id-natural-transformation-map-Precategory C D F)
  is-retraction-natural-transformation-map-inv-natural-isomorphism-map-Precategory =
    is-retraction-natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
      C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G f)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategory
          C D F G f)

  is-natural-isomorphism-map-inv-natural-isomorphism-map-Precategory :
    is-natural-isomorphism-map-Precategory C D G F
      ( natural-transformation-map-inv-natural-isomorphism-map-Precategory)
  is-natural-isomorphism-map-inv-natural-isomorphism-map-Precategory =
    is-natural-isomorphism-map-inv-is-natural-isomorphism-map-Precategory
      C D F G
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G f)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategory
          C D F G f)

  inv-natural-isomorphism-map-Precategory :
    natural-isomorphism-map-Precategory C D G F
  pr1 inv-natural-isomorphism-map-Precategory =
    natural-transformation-map-inv-natural-isomorphism-map-Precategory
  pr2 inv-natural-isomorphism-map-Precategory =
    is-natural-isomorphism-map-inv-natural-isomorphism-map-Precategory
```

### Natural isomorphisms are closed under composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G H : map-Precategory C D)
  (g : natural-transformation-map-Precategory C D G H)
  (f : natural-transformation-map-Precategory C D F G)
  where

  is-natural-isomorphism-map-comp-is-natural-isomorphism-map-Precategory :
    is-natural-isomorphism-map-Precategory C D G H g →
    is-natural-isomorphism-map-Precategory C D F G f →
    is-natural-isomorphism-map-Precategory C D F H
      ( comp-natural-transformation-map-Precategory C D F G H g f)
  is-natural-isomorphism-map-comp-is-natural-isomorphism-map-Precategory
    is-iso-g is-iso-f x =
    is-iso-comp-is-iso-Precategory D (is-iso-g x) (is-iso-f x)
```

### The composition operation on natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G H : map-Precategory C D)
  (g : natural-isomorphism-map-Precategory C D G H)
  (f : natural-isomorphism-map-Precategory C D F G)
  where

  hom-comp-natural-isomorphism-map-Precategory :
    natural-transformation-map-Precategory C D F H
  hom-comp-natural-isomorphism-map-Precategory =
    comp-natural-transformation-map-Precategory C D F G H
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D G H g)
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G f)

  is-natural-isomorphism-map-comp-natural-isomorphism-map-Precategory :
    is-natural-isomorphism-map-Precategory C D F H
      ( hom-comp-natural-isomorphism-map-Precategory)
  is-natural-isomorphism-map-comp-natural-isomorphism-map-Precategory =
    is-natural-isomorphism-map-comp-is-natural-isomorphism-map-Precategory
      C D F G H
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D G H g)
      ( natural-transformation-map-natural-isomorphism-map-Precategory
          C D F G f)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategory
          C D G H g)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategory
          C D F G f)

  comp-natural-isomorphism-map-Precategory :
    natural-isomorphism-map-Precategory C D F H
  pr1 comp-natural-isomorphism-map-Precategory =
    hom-comp-natural-isomorphism-map-Precategory
  pr2 comp-natural-isomorphism-map-Precategory =
    is-natural-isomorphism-map-comp-natural-isomorphism-map-Precategory

  natural-transformation-map-inv-comp-natural-isomorphism-map-Precategory :
    natural-transformation-map-Precategory C D H F
  natural-transformation-map-inv-comp-natural-isomorphism-map-Precategory =
    natural-transformation-map-inv-natural-isomorphism-map-Precategory C D F H
      ( comp-natural-isomorphism-map-Precategory)

  is-section-inv-comp-natural-isomorphism-map-Precategory :
    ( comp-natural-transformation-map-Precategory C D H F H
      ( hom-comp-natural-isomorphism-map-Precategory)
      ( natural-transformation-map-inv-comp-natural-isomorphism-map-Precategory)) ＝
    ( id-natural-transformation-map-Precategory C D H)
  is-section-inv-comp-natural-isomorphism-map-Precategory =
    is-section-natural-transformation-map-inv-natural-isomorphism-map-Precategory
      C D F H comp-natural-isomorphism-map-Precategory

  is-retraction-inv-comp-natural-isomorphism-map-Precategory :
    ( comp-natural-transformation-map-Precategory C D F H F
      ( natural-transformation-map-inv-comp-natural-isomorphism-map-Precategory)
      ( hom-comp-natural-isomorphism-map-Precategory)) ＝
    ( id-natural-transformation-map-Precategory C D F)
  is-retraction-inv-comp-natural-isomorphism-map-Precategory =
    is-retraction-natural-transformation-map-inv-natural-isomorphism-map-Precategory
      C D F H comp-natural-isomorphism-map-Precategory
```

### Groupoid laws of natural isomorphisms in precategories

#### Composition of natural isomorphisms satisfies the unit laws

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  (f : natural-isomorphism-map-Precategory C D F G)
  where

  left-unit-law-comp-natural-isomorphism-map-Precategory :
    comp-natural-isomorphism-map-Precategory C D F G G
      ( id-natural-isomorphism-map-Precategory C D G)
      ( f) ＝
    f
  left-unit-law-comp-natural-isomorphism-map-Precategory =
    eq-eq-natural-transformation-map-natural-isomorphism-map-Precategory C D F G
      ( comp-natural-isomorphism-map-Precategory C D F G G
        ( id-natural-isomorphism-map-Precategory C D G) f)
      ( f)
      ( left-unit-law-comp-natural-transformation-map-Precategory C D F G
        ( natural-transformation-map-natural-isomorphism-map-Precategory
            C D F G f))

  right-unit-law-comp-natural-isomorphism-map-Precategory :
    comp-natural-isomorphism-map-Precategory C D F F G f
      ( id-natural-isomorphism-map-Precategory C D F) ＝
    f
  right-unit-law-comp-natural-isomorphism-map-Precategory =
    eq-eq-natural-transformation-map-natural-isomorphism-map-Precategory C D F G
      ( comp-natural-isomorphism-map-Precategory C D F F G f
        ( id-natural-isomorphism-map-Precategory C D F))
      ( f)
      ( right-unit-law-comp-natural-transformation-map-Precategory C D F G
        ( natural-transformation-map-natural-isomorphism-map-Precategory
            C D F G f))
```

#### Composition of natural isomorphisms is associative

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G H I : map-Precategory C D)
  (f : natural-isomorphism-map-Precategory C D F G)
  (g : natural-isomorphism-map-Precategory C D G H)
  (h : natural-isomorphism-map-Precategory C D H I)
  where

  associative-comp-natural-isomorphism-map-Precategory :
    ( comp-natural-isomorphism-map-Precategory C D F G I
      ( comp-natural-isomorphism-map-Precategory C D G H I h g)
      ( f)) ＝
    ( comp-natural-isomorphism-map-Precategory C D F H I h
      ( comp-natural-isomorphism-map-Precategory C D F G H g f))
  associative-comp-natural-isomorphism-map-Precategory =
    eq-eq-natural-transformation-map-natural-isomorphism-map-Precategory C D F I
      ( comp-natural-isomorphism-map-Precategory C D F G I
        ( comp-natural-isomorphism-map-Precategory C D G H I h g)
        ( f))
      ( comp-natural-isomorphism-map-Precategory C D F H I h
        ( comp-natural-isomorphism-map-Precategory C D F G H g f))
      ( associative-comp-natural-transformation-map-Precategory C D F G H I
        ( natural-transformation-map-natural-isomorphism-map-Precategory
            C D F G f)
        ( natural-transformation-map-natural-isomorphism-map-Precategory
            C D G H g)
        ( natural-transformation-map-natural-isomorphism-map-Precategory
            C D H I h))
```

#### Composition of natural isomorphisms satisfies inverse laws

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  (f : natural-isomorphism-map-Precategory C D F G)
  where

  left-inverse-law-comp-natural-isomorphism-map-Precategory :
    ( comp-natural-isomorphism-map-Precategory C D F G F
      ( inv-natural-isomorphism-map-Precategory C D F G f)
      ( f)) ＝
    ( id-natural-isomorphism-map-Precategory C D F)
  left-inverse-law-comp-natural-isomorphism-map-Precategory =
    eq-eq-natural-transformation-map-natural-isomorphism-map-Precategory C D F F
      ( comp-natural-isomorphism-map-Precategory C D F G F
        ( inv-natural-isomorphism-map-Precategory C D F G f) f)
      ( id-natural-isomorphism-map-Precategory C D F)
      ( is-retraction-natural-transformation-map-inv-natural-isomorphism-map-Precategory
          C D F G f)

  right-inverse-law-comp-natural-isomorphism-map-Precategory :
    ( comp-natural-isomorphism-map-Precategory C D G F G
      ( f)
      ( inv-natural-isomorphism-map-Precategory C D F G f)) ＝
    ( id-natural-isomorphism-map-Precategory C D G)
  right-inverse-law-comp-natural-isomorphism-map-Precategory =
    eq-eq-natural-transformation-map-natural-isomorphism-map-Precategory C D G G
      ( comp-natural-isomorphism-map-Precategory C D G F G
        ( f)
        ( inv-natural-isomorphism-map-Precategory C D F G f))
      ( id-natural-isomorphism-map-Precategory C D G)
      ( is-section-natural-transformation-map-inv-natural-isomorphism-map-Precategory
          C D F G f)
```

### When the type of natural transformations is a proposition, the type of natural isomorphisms is a proposition

The type of natural isomorphisms between maps `F` and `G` is a subtype of
`natural-transformation F G`, so when this type is a proposition, then the type
of natural isomorphisms from `F` to `G` form a proposition.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  where

  is-prop-natural-isomorphism-map-Precategory :
    is-prop (natural-transformation-map-Precategory C D F G) →
    is-prop (natural-isomorphism-map-Precategory C D F G)
  is-prop-natural-isomorphism-map-Precategory =
    is-prop-type-subtype
      ( is-natural-isomorphism-map-prop-hom-Precategory C D F G)

  natural-isomorphism-map-prop-Precategory :
    is-prop (natural-transformation-map-Precategory C D F G) →
    Prop (l1 ⊔ l2 ⊔ l4)
  pr1 (natural-isomorphism-map-prop-Precategory _) =
    natural-isomorphism-map-Precategory C D F G
  pr2 (natural-isomorphism-map-prop-Precategory is-prop-hom-C-F-G) =
    is-prop-natural-isomorphism-map-Precategory is-prop-hom-C-F-G
```

### Functoriality of `natural-isomorphism-map-eq`

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G H : map-Precategory C D)
  where

  preserves-concat-natural-isomorphism-map-eq-Precategory :
    (p : F ＝ G) (q : G ＝ H) →
    natural-isomorphism-map-eq-Precategory C D F H (p ∙ q) ＝
    comp-natural-isomorphism-map-Precategory C D F G H
      ( natural-isomorphism-map-eq-Precategory C D G H q)
      ( natural-isomorphism-map-eq-Precategory C D F G p)
  preserves-concat-natural-isomorphism-map-eq-Precategory refl q =
    inv
      ( right-unit-law-comp-natural-isomorphism-map-Precategory C D F H
        ( natural-isomorphism-map-eq-Precategory C D G H q))
```
