# Cartesian products of pointed types

```agda
module structured-types.cartesian-products-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-types
```

</details>

## Idea

The cartesian product of two pointed types `A , a` and `B , b` is defined as
`A × B , (a , b)`

## Definition

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  product-Pointed-Type : Pointed-Type (l1 ⊔ l2)
  pr1 product-Pointed-Type = type-Pointed-Type A × type-Pointed-Type B
  pr2 product-Pointed-Type = pt-Pointed-Type A , pt-Pointed-Type B
```
