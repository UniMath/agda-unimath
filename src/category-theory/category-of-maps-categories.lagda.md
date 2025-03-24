# The category of maps and natural transformations between two categories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.category-of-maps-categories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext univalence truncations
open import category-theory.commuting-squares-of-morphisms-in-precategories funext univalence truncations
open import category-theory.isomorphisms-in-categories funext univalence truncations
open import category-theory.isomorphisms-in-precategories funext univalence truncations
open import category-theory.maps-categories funext univalence truncations
open import category-theory.maps-precategories funext univalence truncations
open import category-theory.natural-isomorphisms-maps-categories funext univalence truncations
open import category-theory.natural-isomorphisms-maps-precategories funext univalence truncations
open import category-theory.natural-transformations-maps-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations
open import category-theory.precategory-of-maps-precategories funext univalence truncations

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.functoriality-dependent-function-types funext univalence
open import foundation.functoriality-dependent-pair-types funext
open import foundation.identity-types funext
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice funext
open import foundation.univalence funext univalence
open import foundation.universe-levels
```

</details>

## Idea

[Maps](category-theory.maps-categories.md) between
[categories](category-theory.categories.md) and
[natural transformations](category-theory.natural-transformations-maps-categories.md)
between them form another category whose identity map and composition structure
are inherited pointwise from the codomain category. This is called the
**category of maps between categories**.

## Lemmas

### Extensionality of maps of precategories when the codomain is a category

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (is-category-D : is-category-Precategory D)
  where

  equiv-natural-isomorphism-htpy-map-is-category-Precategory :
    (F G : map-Precategory C D) →
    ( htpy-map-Precategory C D F G) ≃
    ( natural-isomorphism-map-Precategory C D F G)
  equiv-natural-isomorphism-htpy-map-is-category-Precategory F G =
      ( equiv-right-swap-Σ) ∘e
      ( equiv-Σ-equiv-base
        ( is-natural-transformation-map-Precategory C D F G ∘ pr1)
        ( ( distributive-Π-Σ) ∘e
          ( equiv-Π-equiv-family
            ( λ x →
              extensionality-obj-Category
                ( D , is-category-D)
                ( obj-map-Precategory C D F x)
                ( obj-map-Precategory C D G x)))))

  extensionality-map-is-category-Precategory :
    (F G : map-Precategory C D) →
    ( F ＝ G) ≃
    ( natural-isomorphism-map-Precategory C D F G)
  extensionality-map-is-category-Precategory F G =
    ( equiv-natural-isomorphism-htpy-map-is-category-Precategory F G) ∘e
    ( equiv-htpy-eq-map-Precategory C D F G)
```

### When the codomain is a category the map precategory is a category

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (is-category-D : is-category-Precategory D)
  where

  abstract
    is-category-map-precategory-is-category-Precategory :
      is-category-Precategory (map-precategory-Precategory C D)
    is-category-map-precategory-is-category-Precategory F G =
      is-equiv-htpy-equiv
        ( ( equiv-iso-map-natural-isomorphism-map-Precategory C D F G) ∘e
          ( extensionality-map-is-category-Precategory C D is-category-D F G))
        ( λ where
          refl →
            compute-iso-map-natural-isomorphism-map-eq-Precategory C D F G refl)
```

## Definitions

### The category of maps and natural transformations between categories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2) (D : Category l3 l4)
  where

  map-category-Category :
    Category (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  pr1 map-category-Category =
    map-precategory-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
  pr2 map-category-Category =
    is-category-map-precategory-is-category-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( is-category-Category D)

  extensionality-map-Category :
    (F G : map-Category C D) →
    (F ＝ G) ≃ natural-isomorphism-map-Category C D F G
  extensionality-map-Category F G =
    ( equiv-natural-isomorphism-map-iso-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D) F G) ∘e
    ( extensionality-obj-Category map-category-Category F G)

  eq-natural-isomorphism-map-Category :
    (F G : map-Category C D) →
    natural-isomorphism-map-Category C D F G → F ＝ G
  eq-natural-isomorphism-map-Category F G =
    map-inv-equiv (extensionality-map-Category F G)
```
