# Function categories

```agda
module category-theory.function-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.dependent-products-of-categories
open import category-theory.precategories

open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Given a [category](category-theory.categories.md) `C` and any type `I`, the
function type `I → C` is a category consisting of functions taking `i : I` to an
object of `C`. Every component of the structure is given pointwise.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) (C : Category l2 l3)
  where

  function-Category : Category (l1 ⊔ l2) (l1 ⊔ l3)
  function-Category = Π-Category I (λ _ → C)

  precategory-function-Category : Precategory (l1 ⊔ l2) (l1 ⊔ l3)
  precategory-function-Category = precategory-Category function-Category

  is-category-precategory-function-Category :
    is-category-Precategory precategory-function-Category
  is-category-precategory-function-Category =
    is-category-Category function-Category

  obj-function-Category : UU (l1 ⊔ l2)
  obj-function-Category = obj-Category function-Category

  hom-function-Category :
    obj-function-Category → obj-function-Category → Set (l1 ⊔ l3)
  hom-function-Category = hom-Category function-Category

  type-hom-function-Category :
    obj-function-Category → obj-function-Category → UU (l1 ⊔ l3)
  type-hom-function-Category = type-hom-Category function-Category

  comp-hom-function-Category :
    {x y z : obj-function-Category} →
    type-hom-function-Category y z →
    type-hom-function-Category x y →
    type-hom-function-Category x z
  comp-hom-function-Category = comp-hom-Category function-Category

  associative-comp-hom-function-Category :
    {x y z w : obj-function-Category}
    (h : type-hom-function-Category z w)
    (g : type-hom-function-Category y z)
    (f : type-hom-function-Category x y) →
    ( comp-hom-function-Category (comp-hom-function-Category h g) f) ＝
    ( comp-hom-function-Category h (comp-hom-function-Category g f))
  associative-comp-hom-function-Category =
    associative-comp-hom-Category function-Category

  associative-composition-structure-function-Category :
    associative-composition-structure-Set hom-function-Category
  associative-composition-structure-function-Category =
    associative-composition-structure-Category function-Category

  id-hom-function-Category :
    {x : obj-function-Category} → type-hom-function-Category x x
  id-hom-function-Category = id-hom-Category function-Category

  left-unit-law-comp-hom-function-Category :
    {x y : obj-function-Category}
    (f : type-hom-function-Category x y) →
    comp-hom-function-Category id-hom-function-Category f ＝ f
  left-unit-law-comp-hom-function-Category =
    left-unit-law-comp-hom-Category function-Category

  right-unit-law-comp-hom-function-Category :
    {x y : obj-function-Category} (f : type-hom-function-Category x y) →
    comp-hom-function-Category f id-hom-function-Category ＝ f
  right-unit-law-comp-hom-function-Category =
    right-unit-law-comp-hom-Category function-Category

  is-unital-function-Category :
    is-unital-composition-structure-Set
      hom-function-Category
      associative-composition-structure-function-Category
  is-unital-function-Category =
    is-unital-composition-structure-Category function-Category
```
