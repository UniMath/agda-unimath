# Function left modules on rings

```agda
module linear-algebra.function-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.dependent-products-left-modules-rings
open import linear-algebra.left-modules-rings

open import ring-theory.rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a type `X` and a [left module](linear-algebra.left-modules-rings.md) `M`
over a [ring](ring-theory.rings.md) `R`, the functions `X → M` form a left
module over `R`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (X : UU l3)
  where

  function-left-module-Ring : left-module-Ring (l2 ⊔ l3) R
  function-left-module-Ring = Π-left-module-Ring R X (λ _ → M)
```
