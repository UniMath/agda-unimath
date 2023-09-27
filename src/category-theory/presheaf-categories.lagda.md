# Presheaf categories

```agda
module category-theory.presheaf-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.category-of-functors
open import category-theory.category-of-functors-small-large-categories
open import category-theory.category-of-maps-categories
open import category-theory.commuting-squares-of-morphisms-in-large-precategories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.functors-small-large-categories
open import category-theory.functors-small-large-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-large-categories
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.maps-categories
open import category-theory.maps-precategories
open import category-theory.maps-small-large-categories
open import category-theory.maps-small-large-precategories
open import category-theory.natural-isomorphisms-categories
open import category-theory.natural-isomorphisms-maps-categories
open import category-theory.natural-isomorphisms-maps-precategories
open import category-theory.natural-isomorphisms-precategories
open import category-theory.natural-transformations-maps-small-large-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories
open import category-theory.precategory-of-functors-small-large-precategories
open import category-theory.precategory-of-maps-small-large-precategories

open import foundation.action-on-identifications-binary-functions
open import foundation.category-of-sets
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

Given any [precategory](category-theory.precategories.md) `C`, we can form its
**presheaf category** as the
[large category](category-theory.large-categories.md) of
[functors](category-theory.functors-small-large-precategories.md) from the
[opposite precategory](category-theory.opposite-precategories.md) of `C`, into
the [large category of sets](foundation.category-of-sets.md)

```text
  Cᵒᵖ → Set.
```

Dually, we can form the **copresheaf category** of `C` by taking the large
functor category

```text
  C → Set.
```

## Definition

### The copresheaf category of a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  copresheaf-Large-Precategory :
    Large-Precategory (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  copresheaf-Large-Precategory =
    functor-large-precategory-Small-Large-Precategory C Set-Large-Precategory

  copresheaf-Large-Category :
    Large-Category (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  large-precategory-Large-Category copresheaf-Large-Category =
    copresheaf-Large-Precategory
  is-large-category-Large-Category copresheaf-Large-Category =
    is-large-category-functor-large-precategory-is-large-category-Small-Large-Precategory
        ( C)
        ( Set-Large-Precategory)
        ( is-large-category-Set-Large-Precategory)
```

### The presheaf category of a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  presheaf-Large-Precategory :
    Large-Precategory (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  presheaf-Large-Precategory =
    copresheaf-Large-Precategory (opposite-Precategory C)

  presheaf-Large-Category :
    Large-Category (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l l' → l1 ⊔ l2 ⊔ l ⊔ l')
  presheaf-Large-Category =
    copresheaf-Large-Category (opposite-Precategory C)
```
