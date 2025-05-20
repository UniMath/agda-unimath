# Sorted lists

```agda
module lists.sorted-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import lists.arrays
open import lists.lists
open import lists.sorted-tuples
open import lists.tuples

open import order-theory.decidable-total-orders
```

</details>

## Idea

We define a sorted list to be a list such that for every pair of consecutive
entries `x` and `y`, the inequality `x ≤ y` holds.

## Definitions

### The proposition that a list is sorted

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  is-sorted-list-Prop : list (type-Decidable-Total-Order X) → Prop l2
  is-sorted-list-Prop nil = raise-unit-Prop l2
  is-sorted-list-Prop (cons x nil) = raise-unit-Prop l2
  is-sorted-list-Prop (cons x (cons y l)) =
    product-Prop
      ( leq-Decidable-Total-Order-Prop X x y)
      ( is-sorted-list-Prop (cons y l))

  is-sorted-list : list (type-Decidable-Total-Order X) → UU l2
  is-sorted-list l = type-Prop (is-sorted-list-Prop l)

  is-prop-is-sorted-list :
    (l : list (type-Decidable-Total-Order X)) → is-prop (is-sorted-list l)
  is-prop-is-sorted-list l = is-prop-type-Prop (is-sorted-list-Prop l)
```

### The proposition that an element is less or equal than every element in a list

```agda
  is-least-element-list-Prop :
    type-Decidable-Total-Order X →
    list (type-Decidable-Total-Order X) → Prop l2
  is-least-element-list-Prop x nil = raise-unit-Prop l2
  is-least-element-list-Prop x (cons y l) =
    product-Prop
      ( leq-Decidable-Total-Order-Prop X x y)
      ( is-least-element-list-Prop x l)

  is-least-element-list :
    type-Decidable-Total-Order X →
    list (type-Decidable-Total-Order X) → UU l2
  is-least-element-list x l = type-Prop (is-least-element-list-Prop x l)
```

## Properties

### If a list is sorted, then its tail is also sorted

```agda
  is-sorted-tail-is-sorted-list :
    (l : list (type-Decidable-Total-Order X)) →
    is-sorted-list l → is-sorted-list (tail-list l)
  is-sorted-tail-is-sorted-list nil _ = raise-star
  is-sorted-tail-is-sorted-list (cons x nil) s = raise-star
  is-sorted-tail-is-sorted-list (cons x (cons y l)) s = pr2 s
```

### If a list is sorted then its head is less or equal than every element in the list

```agda
  leq-element-in-list-leq-head-is-sorted-list :
    (x y z : type-Decidable-Total-Order X)
    (l : list (type-Decidable-Total-Order X)) →
    is-sorted-list (cons y l) →
    z ∈-list (cons y l) →
    leq-Decidable-Total-Order X x y →
    leq-Decidable-Total-Order X x z
  leq-element-in-list-leq-head-is-sorted-list x .z z l s (is-head .z l) q =
    q
  leq-element-in-list-leq-head-is-sorted-list
    ( x)
    ( y)
    ( z)
    ( cons w l)
    ( s)
    ( is-in-tail .z .y .(cons w l) i)
    ( q) =
    leq-element-in-list-leq-head-is-sorted-list
      ( x)
      ( w)
      ( z)
      ( l)
      ( pr2 s)
      ( i)
      ( transitive-leq-Decidable-Total-Order X x y w (pr1 s) q)
```

### An equivalent definition of being sorted

```agda
  is-sorted-least-element-list-Prop :
    list (type-Decidable-Total-Order X) → Prop l2
  is-sorted-least-element-list-Prop nil = raise-unit-Prop l2
  is-sorted-least-element-list-Prop (cons x l) =
    product-Prop
      ( is-least-element-list-Prop x l)
      ( is-sorted-least-element-list-Prop l)

  is-sorted-least-element-list :
    list (type-Decidable-Total-Order X) → UU l2
  is-sorted-least-element-list l =
    type-Prop (is-sorted-least-element-list-Prop l)

  is-sorted-list-is-sorted-least-element-list :
    (l : list (type-Decidable-Total-Order X)) →
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

### If a tuple `v` of length `n` is sorted, then the list `list-tuple n v` is also sorted

```agda
  is-sorted-list-is-sorted-tuple :
    (n : ℕ) (v : tuple (type-Decidable-Total-Order X) n) →
    is-sorted-tuple X v →
    is-sorted-list (list-tuple n v)
  is-sorted-list-is-sorted-tuple 0 v S = raise-star
  is-sorted-list-is-sorted-tuple 1 (x ∷ v) S = raise-star
  is-sorted-list-is-sorted-tuple (succ-ℕ (succ-ℕ n)) (x ∷ y ∷ v) S =
    pr1 S , is-sorted-list-is-sorted-tuple (succ-ℕ n) (y ∷ v) (pr2 S)
```
