# Pointed cartesian product types

```agda
module structured-types.pointed-cartesian-product-types where
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

Given two pointed types `(A , a)` and `(B , b)`, their cartesian product is
again canonically pointed `(A × B , (a , b))`.

## Definition

```agda
module _
  {l1 l2 : Level}
  where

  prod-Pointed-Type :
    (A : Pointed-Type l1) (B : Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
  pr1 (prod-Pointed-Type (A , a) (B , b)) = A × B
  pr2 (prod-Pointed-Type (A , a) (B , b)) = a , b

  _×*_ = prod-Pointed-Type
```
