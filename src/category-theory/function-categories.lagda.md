# Function categories

```agda
module category-theory.function-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.dependent-products-of-categories
open import category-theory.isomorphisms-in-categories
open import category-theory.precategories

open import foundation.equivalences
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

  is-category-function-Category :
    is-category-Precategory precategory-function-Category
  is-category-function-Category =
    is-category-Category function-Category

  obj-function-Category : UU (l1 ⊔ l2)
  obj-function-Category = obj-Category function-Category

  hom-set-function-Category :
    obj-function-Category → obj-function-Category → Set (l1 ⊔ l3)
  hom-set-function-Category = hom-set-Category function-Category

  hom-function-Category :
    obj-function-Category → obj-function-Category → UU (l1 ⊔ l3)
  hom-function-Category = hom-Category function-Category

  comp-hom-function-Category :
    {x y z : obj-function-Category} →
    hom-function-Category y z →
    hom-function-Category x y →
    hom-function-Category x z
  comp-hom-function-Category = comp-hom-Category function-Category

  associative-comp-hom-function-Category :
    {x y z w : obj-function-Category}
    (h : hom-function-Category z w)
    (g : hom-function-Category y z)
    (f : hom-function-Category x y) →
    comp-hom-function-Category (comp-hom-function-Category h g) f ＝
    comp-hom-function-Category h (comp-hom-function-Category g f)
  associative-comp-hom-function-Category =
    associative-comp-hom-Category function-Category

  inv-associative-comp-hom-function-Category :
    {x y z w : obj-function-Category}
    (h : hom-function-Category z w)
    (g : hom-function-Category y z)
    (f : hom-function-Category x y) →
    comp-hom-function-Category h (comp-hom-function-Category g f) ＝
    comp-hom-function-Category (comp-hom-function-Category h g) f
  inv-associative-comp-hom-function-Category =
    inv-associative-comp-hom-Category function-Category

  associative-composition-operation-function-Category :
    associative-composition-operation-binary-family-Set
      hom-set-function-Category
  associative-composition-operation-function-Category =
    associative-composition-operation-Category function-Category

  id-hom-function-Category :
    {x : obj-function-Category} → hom-function-Category x x
  id-hom-function-Category = id-hom-Category function-Category

  left-unit-law-comp-hom-function-Category :
    {x y : obj-function-Category}
    (f : hom-function-Category x y) →
    comp-hom-function-Category id-hom-function-Category f ＝ f
  left-unit-law-comp-hom-function-Category =
    left-unit-law-comp-hom-Category function-Category

  right-unit-law-comp-hom-function-Category :
    {x y : obj-function-Category} (f : hom-function-Category x y) →
    comp-hom-function-Category f id-hom-function-Category ＝ f
  right-unit-law-comp-hom-function-Category =
    right-unit-law-comp-hom-Category function-Category

  is-unital-function-Category :
    is-unital-composition-operation-binary-family-Set
      hom-set-function-Category
      comp-hom-function-Category
  is-unital-function-Category =
    is-unital-composition-operation-Category function-Category

  extensionality-obj-function-Category :
    (x y : obj-Category function-Category) →
    (x ＝ y) ≃ iso-Category function-Category x y
  extensionality-obj-function-Category =
    extensionality-obj-Category function-Category
```

### Isomorphisms in the function category are fiberwise isomorphisms

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) (C : Category l2 l3)
  {x y : obj-function-Category I C}
  where

  is-fiberwise-iso-is-iso-function-Category :
    (f : hom-function-Category I C x y) →
    is-iso-Category (function-Category I C) f →
    (i : I) → is-iso-Category C (f i)
  is-fiberwise-iso-is-iso-function-Category =
    is-fiberwise-iso-is-iso-Π-Category I (λ _ → C)

  fiberwise-iso-iso-function-Category :
    iso-Category (function-Category I C) x y →
    (i : I) → iso-Category C (x i) (y i)
  fiberwise-iso-iso-function-Category =
    fiberwise-iso-iso-Π-Category I (λ _ → C)

  is-iso-function-is-fiberwise-iso-Category :
    (f : hom-function-Category I C x y) →
    ((i : I) → is-iso-Category C (f i)) →
    is-iso-Category (function-Category I C) f
  is-iso-function-is-fiberwise-iso-Category =
    is-iso-is-fiberwise-iso-Π-Category I (λ _ → C)

  iso-function-fiberwise-iso-Category :
    ((i : I) → iso-Category C (x i) (y i)) →
    iso-Category (function-Category I C) x y
  iso-function-fiberwise-iso-Category =
    iso-fiberwise-iso-Π-Category I (λ _ → C)

  is-equiv-is-fiberwise-iso-is-iso-function-Category :
    (f : hom-function-Category I C x y) →
    is-equiv (is-fiberwise-iso-is-iso-function-Category f)
  is-equiv-is-fiberwise-iso-is-iso-function-Category =
    is-equiv-is-fiberwise-iso-is-iso-Π-Category I (λ _ → C)

  equiv-is-fiberwise-iso-is-iso-function-Category :
    (f : hom-function-Category I C x y) →
    ( is-iso-Category (function-Category I C) f) ≃
    ( (i : I) → is-iso-Category C (f i))
  equiv-is-fiberwise-iso-is-iso-function-Category =
    equiv-is-fiberwise-iso-is-iso-Π-Category I (λ _ → C)

  is-equiv-is-iso-function-is-fiberwise-iso-Category :
    (f : hom-function-Category I C x y) →
    is-equiv (is-iso-function-is-fiberwise-iso-Category f)
  is-equiv-is-iso-function-is-fiberwise-iso-Category =
    is-equiv-is-iso-is-fiberwise-iso-Π-Category I (λ _ → C)

  equiv-is-iso-function-is-fiberwise-iso-Category :
    ( f : hom-function-Category I C x y) →
    ( (i : I) → is-iso-Category C (f i)) ≃
    ( is-iso-Category (function-Category I C) f)
  equiv-is-iso-function-is-fiberwise-iso-Category =
    equiv-is-iso-is-fiberwise-iso-Π-Category I (λ _ → C)

  is-equiv-fiberwise-iso-iso-function-Category :
    is-equiv fiberwise-iso-iso-function-Category
  is-equiv-fiberwise-iso-iso-function-Category =
    is-equiv-fiberwise-iso-iso-Π-Category I (λ _ → C)

  equiv-fiberwise-iso-iso-function-Category :
    ( iso-Category (function-Category I C) x y) ≃
    ( (i : I) → iso-Category C (x i) (y i))
  equiv-fiberwise-iso-iso-function-Category =
    equiv-fiberwise-iso-iso-Π-Category I (λ _ → C)

  is-equiv-iso-function-fiberwise-iso-Category :
    is-equiv iso-function-fiberwise-iso-Category
  is-equiv-iso-function-fiberwise-iso-Category =
    is-equiv-iso-fiberwise-iso-Π-Category I (λ _ → C)

  equiv-iso-function-fiberwise-iso-Category :
    ( (i : I) → iso-Category C (x i) (y i)) ≃
    ( iso-Category (function-Category I C) x y)
  equiv-iso-function-fiberwise-iso-Category =
    equiv-iso-fiberwise-iso-Π-Category I (λ _ → C)
```
