# Dependent products of categories

```agda
module category-theory.dependent-products-of-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.dependent-products-of-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Given a family of [categories](category-theory.categories.md) `Cᵢ` indexed by
`i : I`, the dependent product type `Π(i : I), Cᵢ` is a category consisting of
functions taking `i : I` to an object of `Cᵢ`. Every component of the structure
is given pointwise.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) (C : I → Category l2 l3)
  where

  precategory-Π-Category : Precategory (l1 ⊔ l2) (l1 ⊔ l3)
  precategory-Π-Category = Π-Precategory I (precategory-Category ∘ C)

  is-category-precategory-Π-Category :
    is-category-Precategory precategory-Π-Category
  is-category-precategory-Π-Category x y =
    is-equiv-htpy-equiv
      ( equiv-iso-Π-fiberwise-iso-Precategory I (precategory-Category ∘ C) ∘e
        equiv-Π-equiv-family (λ i → equiv-iso-eq-Category (C i)) ∘e
        equiv-funext)
      ( λ {refl → refl})

  Π-Category : Category (l1 ⊔ l2) (l1 ⊔ l3)
  pr1 Π-Category = Π-Precategory I (precategory-Category ∘ C)
  pr2 Π-Category = is-category-precategory-Π-Category

  obj-Π-Category : UU (l1 ⊔ l2)
  obj-Π-Category = obj-Category Π-Category

  hom-Π-Category :
    obj-Π-Category → obj-Π-Category → Set (l1 ⊔ l3)
  hom-Π-Category = hom-Category Π-Category

  type-hom-Π-Category :
    obj-Π-Category → obj-Π-Category → UU (l1 ⊔ l3)
  type-hom-Π-Category = type-hom-Category Π-Category

  comp-hom-Π-Category :
    {x y z : obj-Π-Category} →
    type-hom-Π-Category y z →
    type-hom-Π-Category x y →
    type-hom-Π-Category x z
  comp-hom-Π-Category = comp-hom-Category Π-Category

  associative-comp-hom-Π-Category :
    {x y z w : obj-Π-Category}
    (h : type-hom-Π-Category z w)
    (g : type-hom-Π-Category y z)
    (f : type-hom-Π-Category x y) →
    ( comp-hom-Π-Category (comp-hom-Π-Category h g) f) ＝
    ( comp-hom-Π-Category h (comp-hom-Π-Category g f))
  associative-comp-hom-Π-Category =
    associative-comp-hom-Category Π-Category

  associative-composition-structure-Π-Category :
    associative-composition-structure-Set hom-Π-Category
  associative-composition-structure-Π-Category =
    associative-composition-structure-Category Π-Category

  id-hom-Π-Category :
    {x : obj-Π-Category} → type-hom-Π-Category x x
  id-hom-Π-Category = id-hom-Category Π-Category

  left-unit-law-comp-hom-Π-Category :
    {x y : obj-Π-Category}
    (f : type-hom-Π-Category x y) →
    comp-hom-Π-Category id-hom-Π-Category f ＝ f
  left-unit-law-comp-hom-Π-Category =
    left-unit-law-comp-hom-Category Π-Category

  right-unit-law-comp-hom-Π-Category :
    {x y : obj-Π-Category} (f : type-hom-Π-Category x y) →
    comp-hom-Π-Category f id-hom-Π-Category ＝ f
  right-unit-law-comp-hom-Π-Category =
    right-unit-law-comp-hom-Category Π-Category

  is-unital-Π-Category :
    is-unital-composition-structure-Set
      hom-Π-Category
      associative-composition-structure-Π-Category
  is-unital-Π-Category = is-unital-composition-structure-Category Π-Category
```
