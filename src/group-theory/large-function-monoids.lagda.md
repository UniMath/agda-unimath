# Large function monoids

```agda
module group-theory.large-function-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.dependent-products-large-monoids
open import group-theory.large-monoids
```

</details>

## Idea

Given a [large monoid](group-theory.large-monoids.md) `M` and an arbitrary type
`A`, `A → M` forms a large monoid.

## Definition

```agda
module _
  {l1 : Level}
  {α : Level → Level}
  {β : Level → Level → Level}
  (A : UU l1)
  (M : Large-Monoid α β)
  where

  function-Large-Monoid :
    Large-Monoid (λ l → l1 ⊔ α l) (λ l2 l3 → l1 ⊔ β l2 l3)
  function-Large-Monoid = Π-Large-Monoid A (λ _ → M)
```
