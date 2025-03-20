# Embedding maps between precategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.embedding-maps-precategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.fully-faithful-maps-precategories funext
open import category-theory.maps-precategories funext
open import category-theory.precategories funext

open import foundation.dependent-pair-types
open import foundation.embeddings funext
open import foundation.propositions funext
open import foundation.universe-levels
```

</details>

## Idea

A [map](category-theory.maps-precategories.md) between
[precategories](category-theory.precategories.md) `C` and `D` is an **embedding
map** if it's an [embedding](foundation-core.embeddings.md) on objects and
[fully faithful](category-theory.fully-faithful-maps-precategories.md). Hence
embedding maps are maps that are embeddings on objects and
[equivalences](foundation-core.equivalences.md) on
hom-[sets](foundation-core.sets.md).

Note that for a map of precategories to be called _an embedding_, it must also
be a [functor](category-theory.functors-precategories.md). This notion is
considered in
[`category-theory.embeddings-precategories`](category-theory.embeddings-precategories.md).

## Definition

### The predicate on maps between precategories of being an embedding map

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : map-Precategory C D)
  where

  is-embedding-map-prop-map-Precategory : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-embedding-map-prop-map-Precategory =
    product-Prop
      ( is-emb-Prop (obj-map-Precategory C D F))
      ( is-fully-faithful-prop-map-Precategory C D F)

  is-embedding-map-map-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-embedding-map-map-Precategory =
    type-Prop is-embedding-map-prop-map-Precategory

  is-prop-is-embedding-map-map-Precategory :
    is-prop is-embedding-map-map-Precategory
  is-prop-is-embedding-map-map-Precategory =
    is-prop-type-Prop is-embedding-map-prop-map-Precategory
```

### The type of embedding maps between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  embedding-map-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  embedding-map-Precategory =
    Σ (map-Precategory C D) (is-embedding-map-map-Precategory C D)

  map-embedding-map-Precategory :
    embedding-map-Precategory → map-Precategory C D
  map-embedding-map-Precategory = pr1

  is-embedding-map-embedding-map-Precategory :
    (e : embedding-map-Precategory) →
    is-embedding-map-map-Precategory C D (map-embedding-map-Precategory e)
  is-embedding-map-embedding-map-Precategory = pr2
```
