# Sorted tuples

```agda
module lists.sorted-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import lists.equivalence-tuples-finite-sequences
open import lists.finite-sequences
open import lists.permutation-tuples
open import lists.tuples

open import order-theory.decidable-total-orders

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We define a {{#concept "sorted tuple" Agda=is-sorted-tuple}} to be a
[tuple](lists.tuples.md) such that for every pair of consecutive elements `x`
and `y`, the [inequality](order-theory.decidable-total-orders.md) `x ≤ y` holds.

## Definitions

### The proposition that a tuple is sorted

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  is-sorted-tuple-Prop :
    {n : ℕ} → tuple (type-Decidable-Total-Order X) n → Prop l2
  is-sorted-tuple-Prop {0} v = raise-unit-Prop l2
  is-sorted-tuple-Prop {1} v = raise-unit-Prop l2
  is-sorted-tuple-Prop {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ v) =
    product-Prop
      ( leq-Decidable-Total-Order-Prop X x y)
      ( is-sorted-tuple-Prop (y ∷ v))

  is-sorted-tuple :
    {n : ℕ} → tuple (type-Decidable-Total-Order X) n → UU l2
  is-sorted-tuple l = type-Prop (is-sorted-tuple-Prop l)
```

### The proposition that an element is less than or equal to every element in a tuple

```agda
  is-least-element-tuple-Prop :
    {n : ℕ} → type-Decidable-Total-Order X →
    tuple (type-Decidable-Total-Order X) n → Prop l2
  is-least-element-tuple-Prop {0} x v = raise-unit-Prop l2
  is-least-element-tuple-Prop {succ-ℕ n} x (y ∷ v) =
    product-Prop
      ( leq-Decidable-Total-Order-Prop X x y)
      ( is-least-element-tuple-Prop x v)

  is-least-element-tuple :
    {n : ℕ} → type-Decidable-Total-Order X →
    tuple (type-Decidable-Total-Order X) n → UU l2
  is-least-element-tuple x v = type-Prop (is-least-element-tuple-Prop x v)
```

## Properties

### If a tuple is sorted, then its tail is also sorted

```agda
  is-sorted-tail-is-sorted-tuple :
    {n : ℕ} →
    (v : tuple (type-Decidable-Total-Order X) (succ-ℕ n)) →
    is-sorted-tuple v → is-sorted-tuple (tail-tuple v)
  is-sorted-tail-is-sorted-tuple {zero-ℕ} (x ∷ empty-tuple) s = raise-star
  is-sorted-tail-is-sorted-tuple {succ-ℕ n} (x ∷ y ∷ v) s = pr2 s

  is-leq-head-head-tail-is-sorted-tuple :
    {n : ℕ} → (v : tuple (type-Decidable-Total-Order X) (succ-ℕ (succ-ℕ n))) →
    is-sorted-tuple v →
    leq-Decidable-Total-Order X (head-tuple v) (head-tuple (tail-tuple v))
  is-leq-head-head-tail-is-sorted-tuple (x ∷ y ∷ v) s = pr1 s
```

### If a tuple `v' ＝ y ∷ v` is sorted then for all elements `x` less than or equal to `y`, `x` is less than or equal to every element in the tuple

```agda
  is-least-element-tuple-is-leq-head-sorted-tuple :
    {n : ℕ}
    (x : type-Decidable-Total-Order X)
    (v : tuple (type-Decidable-Total-Order X) (succ-ℕ n)) →
    is-sorted-tuple v → leq-Decidable-Total-Order X x (head-tuple v) →
    is-least-element-tuple x v
  is-least-element-tuple-is-leq-head-sorted-tuple {zero-ℕ} x (y ∷ v) s p =
    p , raise-star
  is-least-element-tuple-is-leq-head-sorted-tuple {succ-ℕ n} x (y ∷ v) s p =
    p ,
    ( is-least-element-tuple-is-leq-head-sorted-tuple
      ( x)
      ( v)
      ( is-sorted-tail-is-sorted-tuple (y ∷ v) s)
      ( transitive-leq-Decidable-Total-Order
        ( X)
        ( x)
        ( y)
        ( head-tuple v)
        ( is-leq-head-head-tail-is-sorted-tuple (y ∷ v) s)
        ( p)))
```

### An equivalent definition of being sorted

```agda
  is-sorted-least-element-tuple-Prop :
    {n : ℕ} → tuple (type-Decidable-Total-Order X) n → Prop l2
  is-sorted-least-element-tuple-Prop {0} v = raise-unit-Prop l2
  is-sorted-least-element-tuple-Prop {1} v = raise-unit-Prop l2
  is-sorted-least-element-tuple-Prop {succ-ℕ (succ-ℕ n)} (x ∷ v) =
    product-Prop
      ( is-least-element-tuple-Prop x v)
      ( is-sorted-least-element-tuple-Prop v)

  is-sorted-least-element-tuple :
    {n : ℕ} → tuple (type-Decidable-Total-Order X) n → UU l2
  is-sorted-least-element-tuple v =
    type-Prop (is-sorted-least-element-tuple-Prop v)

  is-sorted-least-element-tuple-is-sorted-tuple :
    {n : ℕ}
    (v : tuple (type-Decidable-Total-Order X) n) →
    is-sorted-tuple v → is-sorted-least-element-tuple v
  is-sorted-least-element-tuple-is-sorted-tuple {0} v x = raise-star
  is-sorted-least-element-tuple-is-sorted-tuple {1} v x = raise-star
  is-sorted-least-element-tuple-is-sorted-tuple
    {succ-ℕ (succ-ℕ n)}
    ( x ∷ y ∷ v)
    ( p , q) =
    is-least-element-tuple-is-leq-head-sorted-tuple x (y ∷ v) q p ,
    is-sorted-least-element-tuple-is-sorted-tuple (y ∷ v) q

  is-sorted-tuple-is-sorted-least-element-tuple :
    {n : ℕ}
    (v : tuple (type-Decidable-Total-Order X) n) →
    is-sorted-least-element-tuple v →
    is-sorted-tuple v
  is-sorted-tuple-is-sorted-least-element-tuple {0} v x = raise-star
  is-sorted-tuple-is-sorted-least-element-tuple {1} v x = raise-star
  is-sorted-tuple-is-sorted-least-element-tuple
    {succ-ℕ (succ-ℕ n)}
    (x ∷ y ∷ v)
    (p , q) =
    ( pr1 p) ,
    ( is-sorted-tuple-is-sorted-least-element-tuple (y ∷ v) q)
```

### If the tail of a tuple `v` is sorted and `x ≤ head-tuple v`, then `v` is sorted

```agda
  is-sorted-tuple-is-sorted-tail-is-leq-head-tuple :
    {n : ℕ}
    (v : tuple (type-Decidable-Total-Order X) (succ-ℕ (succ-ℕ n))) →
    is-sorted-tuple (tail-tuple v) →
    (leq-Decidable-Total-Order X (head-tuple v) (head-tuple (tail-tuple v))) →
    is-sorted-tuple v
  is-sorted-tuple-is-sorted-tail-is-leq-head-tuple (x ∷ y ∷ v) s p = p , s
```

### If an element `x` is less than or equal to every element of a tuple `v`, then it is less than or equal to every element of every permutation of `v`

```agda
  is-least-element-fin-sequence-Prop :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (fv : fin-sequence (type-Decidable-Total-Order X) n) →
    Prop l2
  is-least-element-fin-sequence-Prop n x fv =
    Π-Prop (Fin n) (λ k → leq-Decidable-Total-Order-Prop X x (fv k))

  is-least-element-fin-sequence :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (fv : fin-sequence (type-Decidable-Total-Order X) n) →
    UU l2
  is-least-element-fin-sequence n x fv =
    type-Prop (is-least-element-fin-sequence-Prop n x fv)

  is-least-element-permute-fin-sequence :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (fv : fin-sequence (type-Decidable-Total-Order X) n)
    (a : Permutation n) →
    is-least-element-fin-sequence n x fv →
    is-least-element-fin-sequence n x (fv ∘ map-equiv a)
  is-least-element-permute-fin-sequence n x fv a p k =
    p (map-equiv a k)

  is-least-element-tuple-is-least-element-fin-sequence :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (fv : fin-sequence (type-Decidable-Total-Order X) n) →
    is-least-element-fin-sequence n x fv →
    is-least-element-tuple x (tuple-fin-sequence n fv)
  is-least-element-tuple-is-least-element-fin-sequence 0 x fv p = raise-star
  is-least-element-tuple-is-least-element-fin-sequence (succ-ℕ n) x fv p =
    (p (inr star)) ,
    ( is-least-element-tuple-is-least-element-fin-sequence
      ( n)
      ( x)
      ( tail-fin-sequence n fv)
      ( p ∘ inl))

  is-least-element-fin-sequence-is-least-element-tuple :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (v : tuple (type-Decidable-Total-Order X) n) →
    is-least-element-tuple x v →
    is-least-element-fin-sequence n x (fin-sequence-tuple n v)
  is-least-element-fin-sequence-is-least-element-tuple
    ( succ-ℕ n)
    ( x)
    ( y ∷ v)
    ( p , q)
    ( inl k) =
    is-least-element-fin-sequence-is-least-element-tuple n x v q k
  is-least-element-fin-sequence-is-least-element-tuple
    ( succ-ℕ n)
    ( x)
    ( y ∷ v)
    ( p , q)
    ( inr star) =
    p

  is-least-element-permute-tuple :
    {n : ℕ}
    (x : type-Decidable-Total-Order X)
    (v : tuple (type-Decidable-Total-Order X) n)
    (a : Permutation n) →
    is-least-element-tuple x v →
    is-least-element-tuple x (permute-tuple n v a)
  is-least-element-permute-tuple {n} x v a p =
    is-least-element-tuple-is-least-element-fin-sequence
      ( n)
      ( x)
      ( fin-sequence-tuple n v ∘ map-equiv a)
      ( is-least-element-permute-fin-sequence
        ( n)
        ( x)
        ( fin-sequence-tuple n v)
        ( a)
        ( is-least-element-fin-sequence-is-least-element-tuple n x v p))
```
