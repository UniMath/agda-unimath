# Spans of closed intervals in total orders

```agda
module order-theory.spans-closed-intervals-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import order-theory.closed-intervals-total-orders
open import order-theory.join-semilattices
open import order-theory.least-upper-bounds-posets
open import order-theory.poset-closed-intervals-total-orders
open import order-theory.total-orders
```

</details>

## Idea

The
{{#concept "span" Disambiguation="of closed intervals in a total order" Agda=span-closed-interval-Total-Order}}
of two [closed intervals](order-theory.closed-intervals-total-orders.md) in a
[total order](order-theory.total-orders.md) is the smallest interval which
[contains](order-theory.poset-closed-intervals-total-orders.md) both intervals,
or in other words, their
[least upper bound](order-theory.least-upper-bounds-posets.md) in the
[poset](order-theory.posets.md) of the containment relation.

## Definition

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  span-closed-interval-Total-Order :
    ([a,b] [c,d] : closed-interval-Total-Order T) →
    closed-interval-Total-Order T
  span-closed-interval-Total-Order ((a , b) , a≤b) ((c , d) , c≤d) =
    ( (min-Total-Order T a c , max-Total-Order T b d) ,
      transitive-leq-Total-Order T _ a _
        ( transitive-leq-Total-Order T a b _
          ( leq-left-max-Total-Order T b d)
          ( a≤b))
        ( leq-left-min-Total-Order T a c))
```

## Properties

### The span of two closed intervals is their least upper bound

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  abstract
    is-least-binary-upper-bound-span-closed-interval-Total-Order :
      ([a,b] [c,d] : closed-interval-Total-Order T) →
      is-least-binary-upper-bound-Poset
        ( poset-closed-interval-Total-Order T)
        ( [a,b])
        ( [c,d])
        ( span-closed-interval-Total-Order T [a,b] [c,d])
    pr1
      ( is-least-binary-upper-bound-span-closed-interval-Total-Order
        ((a , b) , a≤b) ((c , d) , c≤d) ((e , f) , e≤f))
      ( (e≤a , b≤f) , (e≤c , d≤f)) =
      ( leq-min-leq-both-Total-Order T e a c e≤a e≤c ,
        leq-max-leq-both-Total-Order T b d f b≤f d≤f)
    pr2
      ( is-least-binary-upper-bound-span-closed-interval-Total-Order
        ((a , b) , a≤b) ((c , d) , c≤d) ((e , f) , e≤f))
      ( e≤minac , maxbd≤f) =
      ( ( transitive-leq-Total-Order T e _ a
            ( leq-left-min-Total-Order T a c)
            ( e≤minac) ,
          transitive-leq-Total-Order T b _ f
            ( maxbd≤f)
            ( leq-left-max-Total-Order T b d)) ,
        ( transitive-leq-Total-Order T e _ c
            ( leq-right-min-Total-Order T a c)
            ( e≤minac) ,
          transitive-leq-Total-Order T d _ f
            ( maxbd≤f)
            ( leq-right-max-Total-Order T b d)))
```

### The join semilattice of closed intervals

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  is-join-semilattice-closed-interval-Total-Order :
    is-join-semilattice-Poset (poset-closed-interval-Total-Order T)
  is-join-semilattice-closed-interval-Total-Order [a,b] [c,d] =
    ( span-closed-interval-Total-Order T [a,b] [c,d] ,
      is-least-binary-upper-bound-span-closed-interval-Total-Order T
        ( [a,b])
        ( [c,d]))

  order-theoretic-join-semilattice-closed-interval-Total-Order :
    Order-Theoretic-Join-Semilattice (l1 ⊔ l2) l2
  order-theoretic-join-semilattice-closed-interval-Total-Order =
    ( poset-closed-interval-Total-Order T ,
      is-join-semilattice-closed-interval-Total-Order)
```
