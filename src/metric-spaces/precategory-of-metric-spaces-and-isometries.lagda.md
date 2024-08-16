# The precategory of metric spaces and isometries

```agda
module metric-spaces.precategory-of-metric-spaces-and-isometries where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

The [isometries](metric-spaces.isometry-metric-spaces.md) form a
[precategory](category-theory.precategories.md).

## Definition

```agda
module _
  {l : Level}
  where

  precategory-isometry-Metric-Space : Precategory (lsuc l) l
  precategory-isometry-Metric-Space =
    make-Precategory
      ( Metric-Space l)
      ( set-isometry-function-Metric-Space)
      ( λ {A B C} → comp-isometry-function-Metric-Space A B C)
      ( isometry-id-Metric-Space)
      ( λ {A B C D} h g f →
        eq-isometry-function-Metric-Space
          ( A)
          ( D)
          ( comp-isometry-function-Metric-Space A B D
            ( comp-isometry-function-Metric-Space B C D h g)
            ( f))
          ( comp-isometry-function-Metric-Space A C D
            ( h)
            ( comp-isometry-function-Metric-Space A B C g f))
            ( λ x → refl))
      ( λ {A B} f →
        eq-isometry-function-Metric-Space A B
          ( comp-isometry-function-Metric-Space A B B
            ( isometry-id-Metric-Space B)
            ( f))
          ( f)
          ( λ x → refl))
      ( λ {A B} f →
        eq-isometry-function-Metric-Space A B
          ( comp-isometry-function-Metric-Space A A B
            ( f)
            ( isometry-id-Metric-Space A))
          ( f)
          ( λ x → refl))
```
