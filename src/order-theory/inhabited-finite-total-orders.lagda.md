# Inhabited finite total orders

```agda
module order-theory.inhabited-finite-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.finite-posets
open import order-theory.finite-total-orders
open import order-theory.posets
open import order-theory.total-orders

open import univalent-combinatorics.finite-types
```

</details>

## Definitions

An **inhabited finite total order** is a
[finite total order](order-theory.finite-total-orders.md) of which the
underlying type is [inhabited](foundation.inhabited-types.md).

```agda
module _
  {l1 l2 : Level} (P : Finite-Total-Order l1 l2)
  where

  is-inhabited-Finite-Total-Order-Prop : Prop l1
  is-inhabited-Finite-Total-Order-Prop =
    is-inhabited-Prop (type-Finite-Total-Order P)

  is-inhabited-Finite-Total-Order : UU (l1 ⊔ l2)
  is-inhabited-Finite-Total-Order = is-finite-Poset (poset-Finite-Total-Order P)

  is-property-is-inhabited-Finite-Total-Order :
    is-prop is-inhabited-Finite-Total-Order
  is-property-is-inhabited-Finite-Total-Order =
    is-prop-is-finite-Poset (poset-Finite-Total-Order P)

  is-finite-type-is-inhabited-Finite-Total-Order :
    is-inhabited-Finite-Total-Order → is-finite (type-Finite-Total-Order P)
  is-finite-type-is-inhabited-Finite-Total-Order =
    is-finite-type-is-finite-Poset (poset-Finite-Total-Order P)

is-inhabited-finite-total-order-Poset-Prop :
  {l1 l2 : Level} (P : Poset l1 l2) → Prop (l1 ⊔ l2)
is-inhabited-finite-total-order-Poset-Prop P =
  product-Prop
    ( is-total-prop-Poset P)
    ( product-Prop
      ( is-finite-Poset-Prop P)
      ( is-inhabited-Prop (type-Poset P)))
```
