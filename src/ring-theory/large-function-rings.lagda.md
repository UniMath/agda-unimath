# Large function rings

```agda
module ring-theory.large-function-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import ring-theory.dependent-products-large-rings
open import ring-theory.large-rings
```

</details>

## Idea

Given a [large ring](ring-theory.large-rings.md) `R` and an arbitrary type `A`,
`A → R` forms a large ring.

## Definition

```agda
module _
  {l1 : Level}
  {α : Level → Level}
  {β : Level → Level → Level}
  (A : UU l1)
  (R : Large-Ring α β)
  where

  function-Large-Ring : Large-Ring (λ l → l1 ⊔ α l) (λ l2 l3 → l1 ⊔ β l2 l3)
  function-Large-Ring = Π-Large-Ring A (λ _ → R)
```
