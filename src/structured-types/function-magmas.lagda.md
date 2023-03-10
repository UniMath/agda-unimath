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

<details>


## Idea

Given a magma `M` and a type `X`, the function magma `M^X` consists of
functions from `X` into the underlying type of `M`. The operation on
`M^X` is defined pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Magma l1) (X : UU l2)
  where
  
  type-exp-Magma : UU (l1 ⊔ l2)
  type-exp-Magma = X → type-Magma M

  mul-exp-Magma : type-exp-Magma → type-exp-Magma → type-exp-Magma
  mul-exp-Magma f g x = mul-Magma M (f x) (g x)

  exp-Magma : Magma (l1 ⊔ l2)
  pr1 exp-Magma = type-exp-Magma
  pr2 exp-Magma = mul-exp-Magma
```
