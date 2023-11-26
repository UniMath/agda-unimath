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
  {l1 l2 : Level} (P : Total-Order-𝔽 l1 l2)
  where

  is-inhabited-Total-Order-𝔽-Prop : Prop l1
  is-inhabited-Total-Order-𝔽-Prop = is-inhabited-Prop (type-Total-Order-𝔽 P)

  is-inhabited-Total-Order-𝔽 : UU (l1 ⊔ l2)
  is-inhabited-Total-Order-𝔽 = is-finite-Poset (poset-Total-Order-𝔽 P)

  is-prop-is-inhabited-Total-Order-𝔽 : is-prop is-inhabited-Total-Order-𝔽
  is-prop-is-inhabited-Total-Order-𝔽 =
    is-prop-is-finite-Poset (poset-Total-Order-𝔽 P)

  is-finite-type-is-inhabited-Total-Order-𝔽 :
    is-inhabited-Total-Order-𝔽 → is-finite (type-Total-Order-𝔽 P)
  is-finite-type-is-inhabited-Total-Order-𝔽 =
    is-finite-type-is-finite-Poset (poset-Total-Order-𝔽 P)

is-inhabited-finite-total-order-Poset-Prop :
  {l1 l2 : Level} (P : Poset l1 l2) → Prop (l1 ⊔ l2)
is-inhabited-finite-total-order-Poset-Prop P =
  prod-Prop
    ( is-total-Poset-Prop P)
    ( prod-Prop
      ( is-finite-Poset-Prop P)
      ( is-inhabited-Prop (type-Poset P)))
```
