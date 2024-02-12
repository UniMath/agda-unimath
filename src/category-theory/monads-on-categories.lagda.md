# Monads on categories

```agda
module category-theory.monads-on-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-categories
open import category-theory.monads-on-precategories
open import category-theory.natural-transformations-functors-categories
open import category-theory.pointed-endofunctors-categories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
```

</details>

## Idea

A {{#concept "monad" Disambiguation="on a category" Agda=monad-Category}} on a
[category](category-theory.categories.md) `C` consists of an
[endofunctor](category-theory.functors-categories.md) `T : C → C` together with
two
[natural transformations](category-theory.natural-transformations-functors-categories.md):
`η : 1_C ⇒ T` and `μ : T² ⇒ T`, where `1_C : C → C` is the identity functor for
`C`, and `T²` is the functor `T ∘ T : C → C`. These must satisfy the following
{{#concept "monad laws" Disambiguation="monad on a category"}}:

- **Associativity:** `μ ∘ (T • μ) = μ ∘ (μ • T)`
- The **left unit law:** `μ ∘ (T • η) = 1_T`
- The **right unit law:** `μ ∘ (η • T) = 1_T`.

Here, `•` denotes
[whiskering](category-theory.natural-transformations-functors-precategories.md#whiskering),
and `1_T : T ⇒ T` denotes the identity natural transformation for `T`.

## Definitions

### Multiplication structure on a pointed endofunctor on a category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  (T : pointed-endofunctor-Category C)
  where

  structure-multiplication-pointed-endofunctor-Category : UU (l1 ⊔ l2)
  structure-multiplication-pointed-endofunctor-Category =
    structure-multiplication-pointed-endofunctor-Precategory
      ( precategory-Category C)
      ( T)
```

### Associativity of multiplication on a pointed endofunctor on a category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  (T : pointed-endofunctor-Category C)
  (μ : structure-multiplication-pointed-endofunctor-Category C T)
  where

  associative-mul-pointed-endofunctor-Category : UU (l1 ⊔ l2)
  associative-mul-pointed-endofunctor-Category =
    associative-mul-pointed-endofunctor-Precategory
      ( precategory-Category C)
      ( T)
      ( μ)
```

### The left unit law on a multiplication on a pointed endofunctor

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  (T : pointed-endofunctor-Category C)
  (μ : structure-multiplication-pointed-endofunctor-Category C T)
  where

  left-unit-law-mul-pointed-endofunctor-Category : UU (l1 ⊔ l2)
  left-unit-law-mul-pointed-endofunctor-Category =
    left-unit-law-mul-pointed-endofunctor-Precategory
      ( precategory-Category C)
      ( T)
      ( μ)
```

### The right unit law on a multiplication on a pointed endofunctor

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  (T : pointed-endofunctor-Category C)
  (μ : structure-multiplication-pointed-endofunctor-Category C T)
  where

  right-unit-law-mul-pointed-endofunctor-Category : UU (l1 ⊔ l2)
  right-unit-law-mul-pointed-endofunctor-Category =
    right-unit-law-mul-pointed-endofunctor-Precategory
      ( precategory-Category C)
      ( T)
      ( μ)
```

### The structure of a monad on a pointed endofunctor on a category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  (T : pointed-endofunctor-Category C)
  where

  structure-monad-pointed-endofunctor-Category : UU (l1 ⊔ l2)
  structure-monad-pointed-endofunctor-Category =
    structure-monad-pointed-endofunctor-Precategory
      ( precategory-Category C)
      ( T)
```

### The type of monads on categories

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  monad-Category : UU (l1 ⊔ l2)
  monad-Category = monad-Precategory (precategory-Category C)

  module _
    (T : monad-Category)
    where

    pointed-endofunctor-monad-Category :
      pointed-endofunctor-Category C
    pointed-endofunctor-monad-Category =
      pointed-endofunctor-monad-Precategory (precategory-Category C) T

    endofunctor-monad-Category :
      functor-Category C C
    endofunctor-monad-Category =
      endofunctor-monad-Precategory (precategory-Category C) T

    obj-endofunctor-monad-Category :
      obj-Category C → obj-Category C
    obj-endofunctor-monad-Category =
      obj-endofunctor-monad-Precategory (precategory-Category C) T

    hom-endofunctor-monad-Category :
      {X Y : obj-Category C} →
      hom-Category C X Y →
      hom-Category C
        ( obj-endofunctor-monad-Category X)
        ( obj-endofunctor-monad-Category Y)
    hom-endofunctor-monad-Category =
      hom-endofunctor-monad-Precategory (precategory-Category C) T

    preserves-id-endofunctor-monad-Category :
      (X : obj-Category C) →
      hom-endofunctor-monad-Category (id-hom-Category C {X}) ＝
      id-hom-Category C
    preserves-id-endofunctor-monad-Category =
      preserves-id-endofunctor-monad-Precategory (precategory-Category C) T

    preserves-comp-endofunctor-monad-Category :
      {X Y Z : obj-Category C} →
      (g : hom-Category C Y Z) (f : hom-Category C X Y) →
      hom-endofunctor-monad-Category (comp-hom-Category C g f) ＝
      comp-hom-Category C
        ( hom-endofunctor-monad-Category g)
        ( hom-endofunctor-monad-Category f)
    preserves-comp-endofunctor-monad-Category =
      preserves-comp-endofunctor-monad-Precategory (precategory-Category C) T

    unit-monad-Category :
      pointing-endofunctor-Category C endofunctor-monad-Category
    unit-monad-Category =
      unit-monad-Precategory (precategory-Category C) T

    hom-unit-monad-Category :
      hom-family-functor-Category C C
        ( id-functor-Category C)
        ( endofunctor-monad-Category)
    hom-unit-monad-Category =
      hom-unit-monad-Precategory (precategory-Category C) T

    naturality-unit-monad-Category :
      is-natural-transformation-Category C C
        ( id-functor-Category C)
        ( endofunctor-monad-Category)
        ( hom-unit-monad-Category)
    naturality-unit-monad-Category =
      naturality-unit-monad-Precategory (precategory-Category C) T

    mul-monad-Category :
      structure-multiplication-pointed-endofunctor-Category C
        ( pointed-endofunctor-monad-Category)
    mul-monad-Category =
      mul-monad-Precategory (precategory-Category C) T

    hom-mul-monad-Category :
      hom-family-functor-Category C C
        ( comp-functor-Category C C C
          ( endofunctor-monad-Category)
          ( endofunctor-monad-Category))
        ( endofunctor-monad-Category)
    hom-mul-monad-Category =
      hom-mul-monad-Precategory (precategory-Category C) T

    naturality-mul-monad-Category :
      is-natural-transformation-Category C C
        ( comp-functor-Category C C C
          ( endofunctor-monad-Category)
          ( endofunctor-monad-Category))
        ( endofunctor-monad-Category)
        ( hom-mul-monad-Category)
    naturality-mul-monad-Category =
      naturality-mul-monad-Precategory (precategory-Category C) T

    associative-mul-monad-Category :
      associative-mul-pointed-endofunctor-Category C
        ( pointed-endofunctor-monad-Category)
        ( mul-monad-Category)
    associative-mul-monad-Category =
      associative-mul-monad-Precategory (precategory-Category C) T

    left-unit-law-mul-monad-Category :
      left-unit-law-mul-pointed-endofunctor-Category C
        ( pointed-endofunctor-monad-Category)
        ( mul-monad-Category)
    left-unit-law-mul-monad-Category =
      left-unit-law-mul-monad-Precategory (precategory-Category C) T

    right-unit-law-mul-monad-Category :
      right-unit-law-mul-pointed-endofunctor-Category C
        ( pointed-endofunctor-monad-Category)
        ( mul-monad-Category)
    right-unit-law-mul-monad-Category =
      right-unit-law-mul-monad-Precategory (precategory-Category C) T
```
