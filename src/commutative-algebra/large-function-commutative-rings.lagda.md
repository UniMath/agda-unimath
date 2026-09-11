# Large function commutative rings

```agda
module commutative-algebra.large-function-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.large-commutative-rings

open import foundation.function-extensionality
open import foundation.universe-levels

open import ring-theory.large-function-rings
```

</details>

## Idea

Given a [large commutative ring](commutative-algebra.large-commutative-rings.md)
`R` and an arbitrary type `A`, `A → R` forms a large commutative ring.

## Definition

```agda
module _
  {l1 : Level}
  {α : Level → Level}
  {β : Level → Level → Level}
  (A : UU l1)
  (R : Large-Commutative-Ring α β)
  where

  function-Large-Commutative-Ring :
    Large-Commutative-Ring (λ l → l1 ⊔ α l) (λ l2 l3 → l1 ⊔ β l2 l3)
  large-ring-Large-Commutative-Ring function-Large-Commutative-Ring =
    function-Large-Ring A (large-ring-Large-Commutative-Ring R)
  commutative-mul-Large-Commutative-Ring function-Large-Commutative-Ring f g =
    eq-htpy (λ a → commutative-mul-Large-Commutative-Ring R (f a) (g a))
```
