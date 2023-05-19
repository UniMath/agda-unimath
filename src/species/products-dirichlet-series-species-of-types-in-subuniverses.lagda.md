# Product of Dirichlet series of species of types in subuniverse

```agda
module species.products-dirichlet-series-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.functions
open import foundation.subuniverses
open import foundation.universe-levels

open import species.dirichlet-series-species-of-types-in-subuniverses
open import species.species-of-types-in-subuniverses
```

</details>

## Idea

The product of two Dirichlet series is the pointwise product.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : subuniverse l1 l2)
  (C1 : is-closed-under-products-subuniverse P)
  (Q : global-subuniverse id)
  (H : species-subuniverse-domain l5 P)
  (C2 : preserves-product-species-subuniverse-domain P C1 H)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (X : UU l6)
  where

  product-dirichlet-series-subuniverses : UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  product-dirichlet-series-subuniverses =
    dirichlet-series-species-subuniverses
      ( P)
      ( subuniverse-global-subuniverse Q l3)
      ( C1)
      ( H)
      ( C2)
      ( S)
      ( X) ×
    dirichlet-series-species-subuniverses
      ( P)
      ( subuniverse-global-subuniverse Q l4)
      ( C1)
      ( H)
      ( C2)
      ( T)
      ( X)
```
