# The precategory of metric spaces and functions

```agda
module metric-spaces.precategory-of-metric-spaces-and-functions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

Since the carrier type of any [metric space](metric-spaces.metric-spaces.md) is
a [set](foundation-core.sets.md), they are the objects of a
[precategory](category-theory.precategories.md) where morphisms are
[functions](metric-spaces.functions-metric-spaces.md) between them.

## Definition

```agda
module _
  {l1 l2 : Level}
  where

  precategory-function-Metric-Space :
    Precategory (lsuc l1 ⊔ lsuc l2) l1
  precategory-function-Metric-Space =
    make-Precategory
      ( Metric-Space l1 l2)
      ( set-function-Metric-Space)
      ( λ {A B C} g f → g ∘ f)
      ( λ A → id)
      ( λ {A B C D} h g f → refl)
      ( λ {A B} f → refl)
      ( λ {A B} f → refl)
```
