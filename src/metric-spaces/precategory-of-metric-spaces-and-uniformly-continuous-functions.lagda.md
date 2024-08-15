# The precategory of metric spaces and uniformly continuous functions

```agda
module metric-spaces.precategory-of-metric-spaces-and-uniformly-continuous-functions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

The
[uniformly continuous functions](metric-spaces.uniformly-continuous-functions-metric-spaces.md)
form a [precategory](category-theory.precategories.md).

## Definition

```agda
module _
  {l : Level}
  where

  precategory-uniformly-continuous-function-Metric-Space :
    Precategory (lsuc l) l
  precategory-uniformly-continuous-function-Metric-Space =
    make-Precategory
      ( Metric-Space l)
      ( set-uniformly-continuous-function-Metric-Space)
      ( λ {A B C} → comp-uniformly-continuous-function-Metric-Space A B C)
      ( uniformly-continuous-id-Metric-Space)
      ( λ {A B C D} h g f →
        eq-uniformly-continuous-function-Metric-Space
          ( A)
          ( D)
          ( comp-uniformly-continuous-function-Metric-Space A B D
            ( comp-uniformly-continuous-function-Metric-Space B C D h g)
            ( f))
          ( comp-uniformly-continuous-function-Metric-Space A C D
            ( h)
            ( comp-uniformly-continuous-function-Metric-Space A B C g f))
            ( λ x → refl))
      ( λ {A B} f →
        eq-uniformly-continuous-function-Metric-Space A B
          ( comp-uniformly-continuous-function-Metric-Space A B B
            ( uniformly-continuous-id-Metric-Space B)
            ( f))
          ( f)
          ( λ x → refl))
      ( λ {A B} f →
        eq-uniformly-continuous-function-Metric-Space A B
          ( comp-uniformly-continuous-function-Metric-Space A A B
            ( f)
            ( uniformly-continuous-id-Metric-Space A))
          ( f)
          ( λ x → refl))
```
