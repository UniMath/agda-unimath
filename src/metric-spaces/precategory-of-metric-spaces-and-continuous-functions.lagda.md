# The precategory of metric spaces and continuous functions

```agda
module metric-spaces.precategory-of-metric-spaces-and-continuous-functions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.continuous-functions-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

The [continuous functions](metric-spaces.continuous-functions-metric-spaces.md)
form a [precategory](category-theory.precategories.md).

## Definition

```agda
module _
  {l : Level}
  where

  precategory-continuous-function-Metric-Space : Precategory (lsuc l) l
  precategory-continuous-function-Metric-Space =
    make-Precategory
      ( Metric-Space l)
      ( set-continuous-function-Metric-Space)
      ( λ {A B C} → comp-continuous-function-Metric-Space A B C)
      ( continuous-id-Metric-Space)
      ( λ {A B C D} h g f →
        eq-continuous-function-Metric-Space
          ( A)
          ( D)
          ( comp-continuous-function-Metric-Space A B D
            ( comp-continuous-function-Metric-Space B C D h g)
            ( f))
          ( comp-continuous-function-Metric-Space A C D
            ( h)
            ( comp-continuous-function-Metric-Space A B C g f))
            ( λ x → refl))
      ( λ {A B} f →
        eq-continuous-function-Metric-Space A B
          ( comp-continuous-function-Metric-Space A B B
            ( continuous-id-Metric-Space B)
            ( f))
          ( f)
          ( λ x → refl))
      ( λ {A B} f →
        eq-continuous-function-Metric-Space A B
          ( comp-continuous-function-Metric-Space A A B
            ( f)
            ( continuous-id-Metric-Space A))
          ( f)
          ( λ x → refl))
```
