# Faithful functors between precategories

```agda
module category-theory.faithful-functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.faithful-maps-precategories
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.embeddings
open import foundation.equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A [functor](category-theory.functors-precategories.md) between
[precategories](category-theory.precategories.md) `C` and `D` is **faithful** if
it's an [embedding](foundation-core.embeddings.md) on hom-sets.

Note that embeddings on [sets](foundation-core.sets.md) happen to coincide with
[injections](foundation.injective-maps.md). However, we define faithful functors
in terms of embeddings because this is the notion that generalizes.

## Definition

### The predicate on functors between precategories of being faithful

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-faithful-functor-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-faithful-functor-Precategory =
    is-faithful-map-Precategory C D (map-functor-Precategory C D F)

  is-prop-is-faithful-functor-Precategory :
    is-prop is-faithful-functor-Precategory
  is-prop-is-faithful-functor-Precategory =
    is-prop-is-faithful-map-Precategory C D (map-functor-Precategory C D F)

  is-faithful-prop-functor-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  is-faithful-prop-functor-Precategory =
    is-faithful-prop-map-Precategory C D (map-functor-Precategory C D F)
```

### The type of faithful functors between two precategories

```agda
faithful-functor-Precategory :
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
faithful-functor-Precategory C D =
  Σ (functor-Precategory C D) (is-faithful-functor-Precategory C D)

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : faithful-functor-Precategory C D)
  where

  functor-faithful-functor-Precategory : functor-Precategory C D
  functor-faithful-functor-Precategory = pr1 F

  is-faithful-faithful-functor-Precategory :
    is-faithful-functor-Precategory C D functor-faithful-functor-Precategory
  is-faithful-faithful-functor-Precategory = pr2 F

  obj-faithful-functor-Precategory : obj-Precategory C → obj-Precategory D
  obj-faithful-functor-Precategory =
    obj-functor-Precategory C D functor-faithful-functor-Precategory

  hom-faithful-functor-Precategory :
    {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-faithful-functor-Precategory x)
      ( obj-faithful-functor-Precategory y)
  hom-faithful-functor-Precategory =
    hom-functor-Precategory C D functor-faithful-functor-Precategory
```

### The predicate on functors between precategories of being injective on hom-sets

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-injective-hom-functor-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-injective-hom-functor-Precategory =
    is-injective-hom-map-Precategory C D (map-functor-Precategory C D F)

  is-prop-is-injective-hom-functor-Precategory :
    is-prop is-injective-hom-functor-Precategory
  is-prop-is-injective-hom-functor-Precategory =
    is-prop-is-injective-hom-map-Precategory C D
      ( map-functor-Precategory C D F)

  is-injective-hom-prop-functor-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  is-injective-hom-prop-functor-Precategory =
    is-injective-hom-prop-map-Precategory C D
      ( map-functor-Precategory C D F)
```

## Properties

### A functor of precategories is faithful if and only if it is injective on hom-sets

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-injective-hom-is-faithful-functor-Precategory :
    is-faithful-functor-Precategory C D F →
    is-injective-hom-functor-Precategory C D F
  is-injective-hom-is-faithful-functor-Precategory =
    is-injective-hom-is-faithful-map-Precategory C D
      ( map-functor-Precategory C D F)

  is-faithful-is-injective-hom-functor-Precategory :
    is-injective-hom-functor-Precategory C D F →
    is-faithful-functor-Precategory C D F
  is-faithful-is-injective-hom-functor-Precategory =
    is-faithful-is-injective-hom-map-Precategory C D
      ( map-functor-Precategory C D F)

  is-equiv-is-injective-hom-is-faithful-functor-Precategory :
    is-equiv is-injective-hom-is-faithful-functor-Precategory
  is-equiv-is-injective-hom-is-faithful-functor-Precategory =
    is-equiv-is-injective-hom-is-faithful-map-Precategory C D
      ( map-functor-Precategory C D F)

  is-equiv-is-faithful-is-injective-hom-functor-Precategory :
    is-equiv is-faithful-is-injective-hom-functor-Precategory
  is-equiv-is-faithful-is-injective-hom-functor-Precategory =
    is-equiv-is-faithful-is-injective-hom-map-Precategory C D
      ( map-functor-Precategory C D F)

  equiv-is-injective-hom-is-faithful-functor-Precategory :
    is-faithful-functor-Precategory C D F ≃
    is-injective-hom-functor-Precategory C D F
  equiv-is-injective-hom-is-faithful-functor-Precategory =
    equiv-is-injective-hom-is-faithful-map-Precategory C D
      ( map-functor-Precategory C D F)

  equiv-is-faithful-is-injective-hom-functor-Precategory :
    is-injective-hom-functor-Precategory C D F ≃
    is-faithful-functor-Precategory C D F
  equiv-is-faithful-is-injective-hom-functor-Precategory =
    equiv-is-faithful-is-injective-hom-map-Precategory C D
      ( map-functor-Precategory C D F)
```

### Faithful functors are faithful on isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (is-faithful-F : is-faithful-functor-Precategory C D F)
  where

  is-faithful-on-isos-is-faithful-functor-Precategory :
    (x y : obj-Precategory C) →
    is-emb (preserves-iso-functor-Precategory C D F {x} {y})
  is-faithful-on-isos-is-faithful-functor-Precategory x y =
    is-emb-right-factor _ _
      ( is-emb-inclusion-subtype (is-iso-prop-Precategory D))
      ( is-emb-comp _ _
        ( is-faithful-F x y)
        ( is-emb-inclusion-subtype (is-iso-prop-Precategory C)))
```
