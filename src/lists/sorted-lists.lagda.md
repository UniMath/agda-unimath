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
open import foundation.dependent-pair-types

open import lists.lists

open import order-theory.total-decidable-posets
```

</details>

## Idea

In these file, we define sorted lists.

## Definitions

### The proposition that a list is sorted

```agda
module _
  {l1 l2 : Level} (X : total-decidable-Poset l1 l2)
  where

  is-sorted-list-Prop : list (element-total-decidable-Poset X) → Prop l2
  is-sorted-list-Prop nil = raise-unit-Prop l2
  is-sorted-list-Prop (cons x nil) = raise-unit-Prop l2
  is-sorted-list-Prop (cons x (cons y l)) =
    prod-Prop
      ( leq-total-decidable-poset-Prop X x y)
      ( is-sorted-list-Prop (cons y l))

  is-sorted-list : list (element-total-decidable-Poset X) → UU l2
  is-sorted-list l = type-Prop (is-sorted-list-Prop l)
```

### The proposition that a element is less or equal than every element in a list

```agda
  is-least-element-list-Prop :
    element-total-decidable-Poset X →
    list (element-total-decidable-Poset X) → Prop l2
  is-least-element-list-Prop x nil = raise-unit-Prop l2
  is-least-element-list-Prop x (cons y l) =
    prod-Prop
      ( leq-total-decidable-poset-Prop X x y)
      ( is-least-element-list-Prop x l)

  is-least-element-list :
    element-total-decidable-Poset X →
    list (element-total-decidable-Poset X) → UU l2
  is-least-element-list x l = type-Prop (is-least-element-list-Prop x l)
```

## Properties

### If a list is sorted, then its tail is also sorted.

```agda
  is-sorted-tail-is-sorted-list :
    (l : list (element-total-decidable-Poset X)) →
    is-sorted-list l → is-sorted-list (tail-list l)
  is-sorted-tail-is-sorted-list nil _ = raise-star
  is-sorted-tail-is-sorted-list (cons x nil) s = raise-star
  is-sorted-tail-is-sorted-list (cons x (cons y l)) s = pr2 s

--   is-leq-head-head-tail-is-sorted-list :
--     {n : ℕ} → (l : list (element-total-decidable-Poset X)) →
--     leq-ℕ 2 length-list l →
--     is-sorted-list l →
--     leq-total-decidable-Poset X (head-list v) (head-list (tail-list l))
--   is-leq-head-head-tail-is-sorted-list (cons x (cons y l)) s = pr1 s
```

### If a list `l' ＝ cons y l` is sorted then for all element `x` less or equal than `y`, `x` is less or equal than every element in the list.

```agda
--   is-leq-all-element-list-is-leq-head-sorted-list :
--     {n : ℕ}
--     (x : element-total-decidable-Poset X)
--     (l : list (element-total-decidable-Poset X) (succ-ℕ n)) →
--     is-sorted-list l → leq-total-decidable-Poset X x (head-list l) →
--     is-leq-all-element-list x l
--   is-leq-all-element-list-is-leq-head-sorted-list {zero-ℕ} x (y ∷ l) s p =
--     p , raise-star
--   is-leq-all-element-list-is-leq-head-sorted-list {succ-ℕ n} x (y ∷ l) s p =
--     p ,
--     ( is-leq-all-element-list-is-leq-head-sorted-list
--         ( x)
--         ( l)
--         ( is-sorted-tail-is-sorted-list (y ∷ l) s)
--         ( transitile-leq-total-decidable-Poset
--             ( X)
--             ( x)
--             ( y)
--             ( head-list l)
--             ( is-leq-head-head-tail-is-sorted-list (y ∷ l) s)
--             ( p)))
```

### An equivalent definition of being sorted

```agda
  is-sorted-least-element-list-Prop :
    list (element-total-decidable-Poset X) → Prop l2
  is-sorted-least-element-list-Prop nil = raise-unit-Prop l2
  is-sorted-least-element-list-Prop (cons x l) =
    prod-Prop
      ( is-least-element-list-Prop x l)
      ( is-sorted-least-element-list-Prop l)

  is-sorted-least-element-list :
    list (element-total-decidable-Poset X) → UU l2
  is-sorted-least-element-list l =
    type-Prop (is-sorted-least-element-list-Prop l)


--   is-sorted-least-element-list-is-sorted-list :
--     (l : list (element-total-decidable-Poset X)) →
--     is-sorted-list l → is-sorted-least-element-list l
--   is-sorted-least-element-list-is-sorted-list nil x = raise-star
--   is-sorted-least-element-list-is-sorted-list (cons _ nil) x = raise-star
--   is-sorted-least-element-list-is-sorted-list
--     ( cons x (cons y l))
--     ( p , q) =
--     is-least-element-list-is-leq-head-sorted-list x (cons y l) q p ,
--     is-sorted-least-element-list-is-sorted-list (cons y l) q

  is-sorted-list-is-sorted-least-element-list :
    (l : list (element-total-decidable-Poset X)) →
    is-sorted-least-element-list l → is-sorted-list l
  is-sorted-list-is-sorted-least-element-list nil _ =
    raise-star
  is-sorted-list-is-sorted-least-element-list (cons x nil) _ =
    raise-star
  is-sorted-list-is-sorted-least-element-list
    (cons x (cons y l))
    (p , q) =
    ( pr1 p ,
      is-sorted-list-is-sorted-least-element-list (cons y l) q)
```
