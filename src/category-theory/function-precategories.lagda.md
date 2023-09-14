# Function precategories

```agda
module category-theory.function-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.dependent-products-of-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

Given a [precategory](category-theory.precategories.md) `P` and any type `I`,
the function type `I → P` is a precategory consisting of functions taking
`i : I` to an element of the underlying type of `P`. Every component of the
structure is given pointwise.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) (P : Precategory l2 l3)
  where

  function-Precategory : Precategory (l1 ⊔ l2) (l1 ⊔ l3)
  function-Precategory = Π-Precategory I (λ _ → P)

  obj-function-Precategory : UU (l1 ⊔ l2)
  obj-function-Precategory = obj-Precategory function-Precategory

  hom-function-Precategory :
    obj-function-Precategory → obj-function-Precategory → Set (l1 ⊔ l3)
  hom-function-Precategory = hom-Precategory function-Precategory

  type-hom-function-Precategory :
    obj-function-Precategory → obj-function-Precategory → UU (l1 ⊔ l3)
  type-hom-function-Precategory = type-hom-Precategory function-Precategory

  comp-hom-function-Precategory :
    {x y z : obj-function-Precategory} →
    type-hom-function-Precategory y z →
    type-hom-function-Precategory x y →
    type-hom-function-Precategory x z
  comp-hom-function-Precategory = comp-hom-Precategory function-Precategory

  associative-comp-hom-function-Precategory :
    {x y z w : obj-function-Precategory}
    (h : type-hom-function-Precategory z w)
    (g : type-hom-function-Precategory y z)
    (f : type-hom-function-Precategory x y) →
    ( comp-hom-function-Precategory (comp-hom-function-Precategory h g) f) ＝
    ( comp-hom-function-Precategory h (comp-hom-function-Precategory g f))
  associative-comp-hom-function-Precategory =
    associative-comp-hom-Precategory function-Precategory

  associative-composition-function-Precategory :
    associative-composition-structure-Set hom-function-Precategory
  associative-composition-function-Precategory =
    associative-composition-Precategory function-Precategory

  id-hom-function-Precategory :
    {x : obj-function-Precategory} → type-hom-function-Precategory x x
  id-hom-function-Precategory = id-hom-Precategory function-Precategory

  left-unit-law-comp-hom-function-Precategory :
    {x y : obj-function-Precategory}
    (f : type-hom-function-Precategory x y) →
    comp-hom-function-Precategory id-hom-function-Precategory f ＝ f
  left-unit-law-comp-hom-function-Precategory =
    left-unit-law-comp-hom-Precategory function-Precategory

  right-unit-law-comp-hom-function-Precategory :
    {x y : obj-function-Precategory} (f : type-hom-function-Precategory x y) →
    comp-hom-function-Precategory f id-hom-function-Precategory ＝ f
  right-unit-law-comp-hom-function-Precategory =
    right-unit-law-comp-hom-Precategory function-Precategory

  is-unital-function-Precategory :
    is-unital-composition-structure-Set
      hom-function-Precategory
      associative-composition-function-Precategory
  is-unital-function-Precategory = is-unital-Precategory function-Precategory
```
