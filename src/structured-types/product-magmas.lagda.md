# Products of magmas

```agda
module structured-types.product-magmas where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.magmas
open import structured-types.morphisms-magmas
```

</details>

## Idea

The [product](foundation-core.cartesian-product-types.md) of two
[magmas](structured-types.magmas.md) `M N : Magma l` carries a natural magma
structure.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Magma l1) (N : Magma l2)
  where

  product-Magma : Magma (l1 ⊔ l2)
  pr1 product-Magma = type-Magma M × type-Magma N
  pr2 product-Magma (x , y) (z , w) = mul-Magma M x z , mul-Magma N y w
```
