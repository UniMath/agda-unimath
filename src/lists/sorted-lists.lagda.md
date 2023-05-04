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

open import order-theory.total-decidable-posets
```

</details>

## Idea

In these file, we define sorted lists.

## Definitions

### Lists

```agda
module _
  {l1 l2 : Level} (X : total-Decidable-Poset l1 l2)
  where

  is-sorted-list-Prop : list (element-total-Decidable-Poset X) → Prop l2
  is-sorted-list-Prop nil = raise-unit-Prop l2
  is-sorted-list-Prop (cons x nil) = raise-unit-Prop l2
  is-sorted-list-Prop (cons x (cons y l)) =
    prod-Prop
      ( leq-total-Decidable-Poset-Prop X x y)
      ( is-sorted-list-Prop (cons y l))

  is-sorted-list : list (element-total-Decidable-Poset X) → UU l2
  is-sorted-list l = type-Prop (is-sorted-list-Prop l)
```
