# Function magmas

```agda
module structured-types.function-magmas where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.magmas
```

</details>

## Idea

Given a [magma](structured-types.magmas.md) `M` and a type `X`, the
{{#concept "function magma" Agda=function-Magma}} `M^X` consists of functions
from `X` into the underlying type of `M`. The operation on `M^X` is defined
pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Magma l1) (X : UU l2)
  where

  type-function-Magma : UU (l1 ⊔ l2)
  type-function-Magma = X → type-Magma M

  mul-function-Magma :
    type-function-Magma → type-function-Magma → type-function-Magma
  mul-function-Magma f g x = mul-Magma M (f x) (g x)

  function-Magma : Magma (l1 ⊔ l2)
  pr1 function-Magma = type-function-Magma
  pr2 function-Magma = mul-function-Magma
```
