# The category of functors and natural transformations between two categories

```agda
module category-theory.category-of-functors where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.category-of-maps-of-categories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.functors-categories
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.natural-isomorphisms-maps-precategories
open import category-theory.natural-isomorphisms-precategories
open import category-theory.natural-transformations-precategories
open import category-theory.precategories
open import category-theory.precategory-of-functors
open import category-theory.precategory-of-maps-of-precategories

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

[Functors](category-theory.functors-categories.md) between
[categories](category-theory.categories.md) and
[natural transformations](category-theory.natural-transformations-functors-categories.md)
between them assemble to a new category whose identity functor and composition
structure are inherited pointwise from the codomain category. This is called the
**category of functors**.

## Definitons

### Extensionality of functors of precategories when the codomain is a category

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (is-category-D : is-category-Precategory D)
  where

  extensionality-functor-is-category-Precategory :
    (f g : functor-Precategory C D) →
    ( f ＝ g) ≃
    ( natural-isomorphism-Precategory C D f g)
  extensionality-functor-is-category-Precategory f g =
    ( equiv-natural-isomorphism-htpy-map-is-category-Precategory C D
      ( is-category-D)
      ( map-functor-Precategory C D f)
      ( map-functor-Precategory C D g)) ∘e
    ( equiv-htpy-map-eq-functor-Precategory C D f g)
```

### When the codomain is a category the functor precategory is a category

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (is-category-D : is-category-Precategory D)
  where

  abstract
    is-category-functor-precategory-Precategory :
      is-category-Precategory (functor-precategory-Precategory C D)
    is-category-functor-precategory-Precategory F G =
      is-equiv-htpy-equiv
        ( ( equiv-iso-functor-natural-isomorphism-Precategory C D F G) ∘e
          ( extensionality-functor-is-category-Precategory
              C D is-category-D F G))
        ( λ
          { refl →
            compute-iso-map-natural-isomorphism-map-eq-map-Precategory
              ( C)
              ( D)
              ( map-functor-Precategory C D F)
              ( map-functor-Precategory C D G)
              ( refl)})
```

### The category of functors

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2) (D : Category l3 l4)
  where

  functor-category-Category :
    Category (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  pr1 functor-category-Category =
    functor-precategory-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
  pr2 functor-category-Category =
    is-category-functor-precategory-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( is-category-Category D)
```
