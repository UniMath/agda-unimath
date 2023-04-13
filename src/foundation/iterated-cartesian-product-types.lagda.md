# Iterated cartesian product types

```agda
module foundation.iterated-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists
```

</details>

## Definition

```agda
iterated-product :
  {l : Level} → list (UU l) → UU l
iterated-product {l} nil = raise-unit l
iterated-product (cons A p) = A × iterated-product p
```
