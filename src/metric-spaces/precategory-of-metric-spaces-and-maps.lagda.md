# The precategory of metric spaces and maps

```agda
module metric-spaces.precategory-of-metric-spaces-and-maps where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

Since the carrier type of any [metric space](metric-spaces.metric-spaces.md) is
a [set](foundation-core.sets.md), they are the objects of a
[precategory](category-theory.precategories.md) where morphisms are
[maps](metric-spaces.maps-metric-spaces.md) between them.

## Definition

```agda
module _
  {l1 l2 : Level}
  where

  precategory-map-Metric-Space :
    Precategory (lsuc l1 ⊔ lsuc l2) l1
  precategory-map-Metric-Space =
    make-Precategory
      ( Metric-Space l1 l2)
      ( map-set-Metric-Space)
      ( λ {A B C} g f → g ∘ f)
      ( λ A → id)
      ( λ {A B C D} h g f → refl)
      ( λ {A B} f → refl)
      ( λ {A B} f → refl)
```
