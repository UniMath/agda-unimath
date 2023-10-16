# Embedding maps between precategories

```agda
module category-theory.embedding-maps-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.maps-precategories
open import category-theory.faithful-maps-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.cartesian-product-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.injective-maps
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A [map](category-theory.maps-precategories.md) between
[precategories](category-theory.precategories.md) `C` and `D` is an
**embedding** if it's an embedding on objects and
[faithful](category-theory.faithful-maps-precategories.md). Hence embedding maps
are maps that are embeddings on objects and hom-sets.

Note that for a map of precategories to be called _an embedding_, it must also
be a [functor](category-theory.functors-precategories.md). This notion is
considered in
[`category-theory.embeddings-precategories`](category-theory.embeddings-precategories.md).

## Definition

### The predicate of being an embedding map on maps between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : map-Precategory C D)
  where

  is-embedding-map-prop-map-Precategory : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-embedding-map-prop-map-Precategory =
    prod-Prop
      ( is-emb-Prop (obj-map-Precategory C D F))
      ( is-faithful-prop-map-Precategory C D F)

  is-embedding-map-map-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-embedding-map-map-Precategory =
    type-Prop is-embedding-map-prop-map-Precategory

  is-prop-is-embedding-map-map-Precategory : is-prop is-embedding-map-map-Precategory
  is-prop-is-embedding-map-map-Precategory =
    is-prop-type-Prop is-embedding-map-prop-map-Precategory
```
