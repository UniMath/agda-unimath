# Sorted lists

```agda
module lists.sorted-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists

open import order-theory.decidable-total-orders
```

</details>

## Idea

In these file, we define sorted lists.

## Definitions

### Lists

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  is-sorted-list-Prop : list (type-Decidable-Total-Order X) → Prop l2
  is-sorted-list-Prop nil = raise-unit-Prop l2
  is-sorted-list-Prop (cons x nil) = raise-unit-Prop l2
  is-sorted-list-Prop (cons x (cons y l)) =
    prod-Prop
      ( leq-Decidable-Total-Order-Prop X x y)
      ( is-sorted-list-Prop (cons y l))

  is-sorted-list : list (type-Decidable-Total-Order X) → UU l2
  is-sorted-list l = type-Prop (is-sorted-list-Prop l)
```
