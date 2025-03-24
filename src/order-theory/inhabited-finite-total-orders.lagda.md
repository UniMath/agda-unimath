# Inhabited finite total orders

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module order-theory.inhabited-finite-total-orders
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.inhabited-types funext univalence truncations
open import foundation.propositions funext univalence
open import foundation.universe-levels

open import order-theory.finite-posets funext univalence truncations
open import order-theory.finite-total-orders funext univalence truncations
open import order-theory.posets funext univalence truncations
open import order-theory.total-orders funext univalence truncations

open import univalent-combinatorics.finite-types funext univalence truncations
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
    ( is-total-Poset-Prop P)
    ( product-Prop
      ( is-finite-Poset-Prop P)
      ( is-inhabited-Prop (type-Poset P)))
```
