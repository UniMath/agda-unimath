# Function algebras on commutative rings

```agda
module commutative-algebra.function-algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.dependent-products-algebras-commutative-rings

open import foundation.universe-levels
```

</details>

## Idea

Given a [commutative ring](commutative-algebra.commutative-rings.md) `R`, an
index type `I`, and an
[algebra](commutative-algebra.algebras-commutative-rings.md) `A` over `R`, the
function type `I → A` is an algebra over `R`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (I : UU l2)
  (A : algebra-Commutative-Ring l3 R)
  where

  function-algebra-Commutative-Ring : algebra-Commutative-Ring (l2 ⊔ l3) R
  function-algebra-Commutative-Ring = Π-algebra-Commutative-Ring R I (λ _ → A)
```
