# The precategory of metric spaces and short functions

```agda
module metric-spaces.precategory-of-metric-spaces-and-short-functions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

The [short functions](metric-spaces.short-functions-metric-spaces.md) form a
[precategory](category-theory.precategories.md).

## Definition

```agda
module _
  {l : Level}
  where

  precategory-short-function-Metric-Space : Precategory (lsuc l) l
  precategory-short-function-Metric-Space =
    make-Precategory
      ( Metric-Space l)
      ( set-short-function-Metric-Space)
      ( λ {A B C} → comp-short-function-Metric-Space A B C)
      ( short-id-Metric-Space)
      ( λ {A B C D} h g f →
        eq-short-function-Metric-Space
          ( A)
          ( D)
          ( comp-short-function-Metric-Space A B D
            ( comp-short-function-Metric-Space B C D h g)
            ( f))
          ( comp-short-function-Metric-Space A C D
            ( h)
            ( comp-short-function-Metric-Space A B C g f))
            ( λ x → refl))
      ( λ {A B} f →
        eq-short-function-Metric-Space A B
          ( comp-short-function-Metric-Space A B B
            ( short-id-Metric-Space B)
            ( f))
          ( f)
          ( λ x → refl))
      ( λ {A B} f →
        eq-short-function-Metric-Space A B
          ( comp-short-function-Metric-Space A A B
            ( f)
            ( short-id-Metric-Space A))
          ( f)
          ( λ x → refl))
```
