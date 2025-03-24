# The precategory of metric spaces and functions

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module metric-spaces.precategory-of-metric-spaces-and-functions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories funext univalence truncations

open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces funext univalence truncations
open import metric-spaces.metric-spaces funext univalence truncations
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
      ( set-map-type-Metric-Space)
      ( λ {A B C} g f → g ∘ f)
      ( λ A → id)
      ( λ {A B C D} h g f → refl)
      ( λ {A B} f → refl)
      ( λ {A B} f → refl)
```
