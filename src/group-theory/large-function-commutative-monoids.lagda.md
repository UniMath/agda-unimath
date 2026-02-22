# Large function commutative monoids

```agda
module group-theory.large-function-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.dependent-products-large-commutative-monoids
open import group-theory.large-commutative-monoids
```

</details>

## Idea

Given a [large commutative monoid](group-theory.large-commutative-monoids.md)
`M` and an arbitrary type `A`, `A → M` forms a large commutative monoid.

## Definition

```agda
module _
  {l1 : Level}
  {α : Level → Level}
  {β : Level → Level → Level}
  (A : UU l1)
  (M : Large-Commutative-Monoid α β)
  where

  function-Large-Commutative-Monoid :
    Large-Commutative-Monoid (λ l → l1 ⊔ α l) (λ l2 l3 → l1 ⊔ β l2 l3)
  function-Large-Commutative-Monoid = Π-Large-Commutative-Monoid A (λ _ → M)
```
