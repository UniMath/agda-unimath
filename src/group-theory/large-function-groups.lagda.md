# Large function groups

```agda
module group-theory.large-function-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.dependent-products-large-groups
open import group-theory.large-groups
```

</details>

## Idea

Given a [large group](group-theory.large-groups.md) `G` and an arbitrary type
`A`, `A → G` forms a large group.

## Definition

```agda
module _
  {l1 : Level}
  {α : Level → Level}
  {β : Level → Level → Level}
  (A : UU l1)
  (G : Large-Group α β)
  where

  function-Large-Group : Large-Group (λ l → l1 ⊔ α l) (λ l2 l3 → l1 ⊔ β l2 l3)
  function-Large-Group = Π-Large-Group A (λ _ → G)
```
