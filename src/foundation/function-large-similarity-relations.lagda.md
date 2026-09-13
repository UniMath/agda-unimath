# Function large similarity relations

```agda
module foundation.function-large-similarity-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-large-similarity-relations
open import foundation.large-similarity-relations
open import foundation.universe-levels
```

</details>

## Idea

Given a [large similarity relation](foundation.large-similarity-relations.md) on
`X` and any type `A`, there is an induced large similarity relation on `A → X`.

## Definition

```agda
module _
  {l1 : Level}
  {α : Level → Level}
  {β : Level → Level → Level}
  {X : (l : Level) → UU (α l)}
  (A : UU l1)
  (R : Large-Similarity-Relation β X)
  where

  function-Large-Similarity-Relation :
    Large-Similarity-Relation
      ( λ l2 l3 → l1 ⊔ β l2 l3)
      ( λ l → A → X l)
  function-Large-Similarity-Relation =
    Π-Large-Similarity-Relation A (λ _ → X) (λ _ → R)
```
