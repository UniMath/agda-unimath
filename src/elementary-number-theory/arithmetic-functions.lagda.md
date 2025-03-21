# Arithmetic functions

```agda
module elementary-number-theory.arithmetic-functions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

An arithmetic function is a function from the nonzero natural numbers into a
(commutative) ring. The arithmetic functions form a ring under pointwise
addition and dirichlet convolution.

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  type-arithmetic-functions-Ring : UU l
  type-arithmetic-functions-Ring = nonzero-ℕ → type-Ring R
```
