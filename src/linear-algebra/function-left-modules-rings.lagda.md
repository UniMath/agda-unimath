# Function left modules over rings

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

Given a [ring](ring-theory.rings.md) `R` and an indexing type `I`, the type
`I → R` forms a [left module](linear-algebra.left-modules-rings.md) over `R`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : UU l2)
  where

  function-left-module-Ring : left-module-Ring (l1 ⊔ l2) R
  function-left-module-Ring =
    Π-left-module-Ring R I (λ _ → left-module-ring-Ring R)
```
