# Function cumulative large sets

```agda
module foundation.function-cumulative-large-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.dependent-products-cumulative-large-sets
open import foundation.universe-levels
```

</details>

## Idea

Given an index type `I` and a
[cumulative large set](foundation.cumulative-large-sets.md) `S`, the function
type `I → S` is a cumulative large set.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (I : UU l0)
  (S : Cumulative-Large-Set α β)
  where

  function-Cumulative-Large-Set :
    Cumulative-Large-Set (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  function-Cumulative-Large-Set =
    Π-Cumulative-Large-Set I (λ _ → S)
```
