# Large function commutative monoids

```agda
module group-theory.large-function-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.universe-levels

open import group-theory.large-commutative-monoids
open import group-theory.large-function-monoids
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
  large-monoid-Large-Commutative-Monoid function-Large-Commutative-Monoid =
    function-Large-Monoid A (large-monoid-Large-Commutative-Monoid M)
  commutative-mul-Large-Commutative-Monoid function-Large-Commutative-Monoid
    f g =
    eq-htpy ( λ a → commutative-mul-Large-Commutative-Monoid M (f a) (g a))
```
