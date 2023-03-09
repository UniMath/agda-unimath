# Ideals in preorders

```agda
module order-theory.ideals-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.universe-levels

open import order-theory.lower-types-preorders
open import order-theory.preorders
```

</details>

## Idea

Ideals in preorders are inhabited lower types `L` that contain an upper bound for every pair of elements in `L`.

## Definition

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  is-ideal-lower-type-Preorder :
    {l3 : Level} (L : lower-type-Preorder l3 P) → UU (l1 ⊔ l2 ⊔ l3)
  is-ideal-lower-type-Preorder L =
    ( is-inhabited (element-lower-type-Preorder P L)) ×
    ( (x y : element-lower-type-Preorder P L) →
      is-inhabited
        ( Σ ( element-lower-type-Preorder P L)
            ( λ z →
              ( leq-lower-type-Preorder P L x z) ×
              ( leq-lower-type-Preorder P L y z))))
```
