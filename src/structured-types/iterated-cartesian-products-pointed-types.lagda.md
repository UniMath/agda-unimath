# Iterated cartesian products of pointed types

```agda
module structured-types.iterated-cartesian-products-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.iterated-cartesian-product-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.functoriality-lists
open import lists.lists

open import structured-types.cartesian-products-pointed-types
open import structured-types.pointed-types
```

</details>

## Definition

```agda
iterated-product-Pointed-Type :
  {l : Level} → (L : list (Pointed-Type l)) → Pointed-Type l
iterated-product-Pointed-Type nil = raise-unit _ , raise-star
iterated-product-Pointed-Type (cons x L) =
  product-Pointed-Type x (iterated-product-Pointed-Type L)
```
