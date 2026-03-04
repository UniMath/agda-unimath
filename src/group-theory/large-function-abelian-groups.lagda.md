# Large function abelian groups

```agda
module group-theory.large-function-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.dependent-products-large-abelian-groups
open import group-theory.large-abelian-groups
```

</details>

## Idea

Given a [large abelian group](group-theory.large-abelian-groups.md) `G` and an
arbitrary type `A`, `A → G` forms a large abelian group.

## Definition

```agda
module _
  {l1 : Level}
  {α : Level → Level}
  {β : Level → Level → Level}
  (A : UU l1)
  (G : Large-Ab α β)
  where

  function-Large-Ab : Large-Ab (λ l → l1 ⊔ α l) (λ l2 l3 → l1 ⊔ β l2 l3)
  function-Large-Ab = Π-Large-Ab A (λ _ → G)
```
