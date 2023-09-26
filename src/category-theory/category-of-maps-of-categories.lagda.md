# The category of maps and natural transformations between two categories

```agda
module category-theory.category-of-maps-of-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-categories
open import category-theory.maps-precategories
open import category-theory.natural-isomorphisms-maps-categories
open import category-theory.natural-isomorphisms-maps-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.precategories
open import category-theory.precategory-of-maps-of-precategories

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

[Maps](category-theory.maps-categories.md) between
[categories](category-theory.categories.md) and
[natural transformations](category-theory.natural-transformations-maps-categories.md)
between them assemble to a new category whose identity map and composition
structure are inherited pointwise from the codomain category. This is called the
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
    (f g : map-Precategory C D) →
    ( htpy-map-Precategory C D f g) ≃
    ( natural-isomorphism-map-Precategory C D f g)
  equiv-natural-isomorphism-htpy-map-is-category-Precategory f g =
      ( equiv-right-swap-Σ) ∘e
      ( equiv-Σ
        ( is-natural-transformation-map-Precategory C D f g ∘ pr1)
        ( ( distributive-Π-Σ) ∘e
          ( equiv-Π-equiv-family
            ( λ x →
              extensionality-obj-Category (D , is-category-D)
                ( obj-map-Precategory C D f x)
                ( obj-map-Precategory C D g x))))
        ( λ K →
          equiv-implicit-Π-equiv-family
            ( λ x →
              equiv-implicit-Π-equiv-family
                ( λ y →
                  equiv-Π-equiv-family
                    ( λ a →
                      ( equiv-eq
                        ( ap-binary
                          ( λ p q →
                            coherence-square-hom-Precategory D
                              ( hom-map-Precategory C D f a)
                              ( p)
                              ( q)
                              ( hom-map-Precategory C D g a))
                          ( compute-hom-iso-eq-Precategory D (K x))
                          ( compute-hom-iso-eq-Precategory D (K y)))))))))

  extensionality-map-is-category-Precategory :
    (f g : map-Precategory C D) →
    ( f ＝ g) ≃
    ( natural-isomorphism-map-Precategory C D f g)
  extensionality-map-is-category-Precategory f g =
    ( equiv-natural-isomorphism-htpy-map-is-category-Precategory f g) ∘e
    ( equiv-htpy-eq-map-Precategory C D f g)
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
    is-category-map-precategory-Precategory :
      is-category-Precategory (map-precategory-Precategory C D)
    is-category-map-precategory-Precategory F G =
      is-equiv-htpy-equiv
        ( ( equiv-iso-map-natural-isomorphism-map-Precategory C D F G) ∘e
          ( extensionality-map-is-category-Precategory C D is-category-D F G))
        ( λ
          { refl →
            compute-iso-map-natural-isomorphism-map-eq-Precategory
              C D F G refl})
```

## Definition

### The category of maps of categories

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
    is-category-map-precategory-Precategory
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
