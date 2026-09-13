# Function left modules on rings

```agda
module linear-algebra.function-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import linear-algebra.dependent-products-left-modules-rings
open import linear-algebra.left-modules-rings

open import ring-theory.rings
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

## Properties

### The functions `X → R` form a left module over `R`

```agda
function-left-module-ring-Ring :
  {l1 l2 : Level} (R : Ring l1) → UU l2 → left-module-Ring (l1 ⊔ l2) R
function-left-module-ring-Ring R =
  function-left-module-Ring R (left-module-ring-Ring R)
```
