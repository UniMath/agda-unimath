# Large function semigroups

```agda
module group-theory.large-function-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.sets
open import foundation.universe-levels

open import group-theory.dependent-products-large-semigroups
open import group-theory.large-semigroups
```

</details>

## Idea

Given a [large semigroup](group-theory.large-semigroups.md) `G` and an arbitrary
type `A`, `A → G` forms a large semigroup.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (A : UU l0)
  (G : Large-Semigroup α β)
  where

  function-Large-Semigroup :
    Large-Semigroup (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  function-Large-Semigroup = Π-Large-Semigroup A (λ _ → G)
```
