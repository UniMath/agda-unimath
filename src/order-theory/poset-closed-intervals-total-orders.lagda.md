# The poset of closed intervals in total orders

```agda
module order-theory.poset-closed-intervals-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.intersections-subtypes
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.closed-intervals-total-orders
open import order-theory.greatest-lower-bounds-posets
open import order-theory.join-semilattices
open import order-theory.least-upper-bounds-posets
open import order-theory.poset-closed-intervals-posets
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-orders
```

</details>

## Idea

In a [total order](order-theory.total-orders.md) `T`, the type of
[closed intervals](order-theory.closed-intervals-total-orders.md) in `T` itself
forms a [poset](order-theory.posets.md), with inequality defined by containment
of the corresponding subtypes. Equivalently, `[a,b] ≤ [c,d]` if `c ≤ a` and
`b ≤ d`.

## Definition

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  leq-prop-closed-interval-Total-Order :
    Relation-Prop l2 (closed-interval-Total-Order T)
  leq-prop-closed-interval-Total-Order =
    leq-prop-closed-interval-Poset (poset-Total-Order T)

  leq-closed-interval-Total-Order : Relation l2 (closed-interval-Total-Order T)
  leq-closed-interval-Total-Order =
    leq-closed-interval-Poset (poset-Total-Order T)
```

## Properties

### Containment is a preorder

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  refl-leq-closed-interval-Total-Order :
    is-reflexive (leq-closed-interval-Total-Order T)
  refl-leq-closed-interval-Total-Order =
    refl-leq-closed-interval-Poset (poset-Total-Order T)

  transitive-leq-closed-interval-Total-Order :
    is-transitive (leq-closed-interval-Total-Order T)
  transitive-leq-closed-interval-Total-Order =
    transitive-leq-closed-interval-Poset (poset-Total-Order T)

  is-preorder-leq-closed-interval-Total-Order :
    is-preorder-Relation-Prop (leq-prop-closed-interval-Total-Order T)
  is-preorder-leq-closed-interval-Total-Order =
    is-preorder-leq-closed-interval-Poset (poset-Total-Order T)
```

### Containment is a poset

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  antisymmetric-leq-closed-interval-Total-Order :
    is-antisymmetric (leq-closed-interval-Total-Order T)
  antisymmetric-leq-closed-interval-Total-Order =
    antisymmetric-leq-closed-interval-Poset (poset-Total-Order T)

  poset-closed-interval-Total-Order : Poset (l1 ⊔ l2) l2
  poset-closed-interval-Total-Order =
    poset-closed-interval-Poset (poset-Total-Order T)
```

### Containment of closed intervals is equivalent to containment of subtypes

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  leq-subtype-leq-closed-interval-Total-Order :
    ([a,b] [c,d] : closed-interval-Total-Order T) →
    leq-closed-interval-Total-Order T [a,b] [c,d] →
    ( subtype-closed-interval-Total-Order T [a,b] ⊆
      subtype-closed-interval-Total-Order T [c,d])
  leq-subtype-leq-closed-interval-Total-Order =
    leq-subtype-leq-closed-interval-Poset (poset-Total-Order T)

  leq-closed-interval-leq-subtype-Total-Order :
    ([a,b] [c,d] : closed-interval-Total-Order T) →
    ( subtype-closed-interval-Total-Order T [a,b] ⊆
      subtype-closed-interval-Total-Order T [c,d]) →
    leq-closed-interval-Total-Order T [a,b] [c,d]
  leq-closed-interval-leq-subtype-Total-Order =
    leq-closed-interval-leq-subtype-Poset (poset-Total-Order T)

  leq-subtype-iff-leq-closed-interval-Total-Order :
    ([a,b] [c,d] : closed-interval-Total-Order T) →
    ( leq-closed-interval-Total-Order T [a,b] [c,d] ↔
      ( subtype-closed-interval-Total-Order T [a,b] ⊆
        subtype-closed-interval-Total-Order T [c,d]))
  leq-subtype-iff-leq-closed-interval-Total-Order =
    leq-subtype-iff-leq-closed-interval-Poset (poset-Total-Order T)
```

### The condition of closed intervals intersecting

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  intersect-prop-closed-interval-Total-Order :
    Relation-Prop l2 (closed-interval-Total-Order T)
  intersect-prop-closed-interval-Total-Order ((a , b) , _) ((c , d) , _) =
    leq-prop-Total-Order T a d ∧ leq-prop-Total-Order T c b

  intersect-closed-interval-Total-Order :
    Relation l2 (closed-interval-Total-Order T)
  intersect-closed-interval-Total-Order =
    type-Relation-Prop intersect-prop-closed-interval-Total-Order

  refl-intersect-closed-interval-Total-Order :
    ([a,b] : closed-interval-Total-Order T) →
    intersect-closed-interval-Total-Order [a,b] [a,b]
  refl-intersect-closed-interval-Total-Order ((a , b) , a≤b) =
    ( a≤b , a≤b)
```

### If two closed intervals intersect, their intersection is a closed interval

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  intersection-closed-interval-Total-Order :
    ([a,b] [c,d] : closed-interval-Total-Order T) →
    intersect-closed-interval-Total-Order T [a,b] [c,d] →
    closed-interval-Total-Order T
  intersection-closed-interval-Total-Order
    ((a , b) , a≤b) ((c , d) , c≤d) (a≤d , c≤b) =
    ( (max-Total-Order T a c , min-Total-Order T b d) ,
      leq-min-leq-both-Total-Order
        ( T)
        ( max-Total-Order T a c)
        ( b)
        ( d)
        ( leq-max-leq-both-Total-Order T a c b a≤b c≤b)
        ( leq-max-leq-both-Total-Order T a c d a≤d c≤d))

  abstract
    is-intersection-closed-interval-Total-Order :
      ([a,b] [c,d] : closed-interval-Total-Order T) →
      (H : intersect-closed-interval-Total-Order T [a,b] [c,d]) →
      subtype-closed-interval-Total-Order T
        ( intersection-closed-interval-Total-Order [a,b] [c,d] H) ＝
      intersection-subtype
        ( subtype-closed-interval-Total-Order T [a,b])
        ( subtype-closed-interval-Total-Order T [c,d])
    is-intersection-closed-interval-Total-Order
      ((a , b) , a≤b) ((c , d) , c≤d) (a≤d , c≤b) =
      eq-sim-subtype _ _
        ( ( λ x (maxac≤x , x≤minbd) →
            ( ( transitive-leq-Total-Order T a _ x
                  ( maxac≤x)
                  ( leq-left-max-Total-Order T a c) ,
                transitive-leq-Total-Order T x _ b
                  ( leq-left-min-Total-Order T b d)
                  ( x≤minbd)) ,
              ( transitive-leq-Total-Order T c _ x
                  ( maxac≤x)
                  ( leq-right-max-Total-Order T a c) ,
                transitive-leq-Total-Order T x _ d
                  ( leq-right-min-Total-Order T b d)
                  ( x≤minbd)))) ,
          ( λ x ((a≤x , x≤b) , (c≤x , x≤d)) →
            ( leq-max-leq-both-Total-Order T a c x a≤x c≤x ,
              leq-min-leq-both-Total-Order T x b d x≤b x≤d)))

    intersect-closed-interval-intersect-subtype-Total-Order :
      ([a,b] [c,d] : closed-interval-Total-Order T) →
      intersect-subtype
        ( subtype-closed-interval-Total-Order T [a,b])
        ( subtype-closed-interval-Total-Order T [c,d]) →
      intersect-closed-interval-Total-Order T [a,b] [c,d]
    intersect-closed-interval-intersect-subtype-Total-Order
      [a,b]@((a , b) , a≤b) [c,d]@((c , d) , c≤d) ∃x =
      let
        open
          do-syntax-trunc-Prop
            ( intersect-prop-closed-interval-Total-Order T [a,b] [c,d])
      in do
        (x , (a≤x , x≤b) , (c≤x , x≤d)) ← ∃x
        ( transitive-leq-Total-Order T a x d x≤d a≤x ,
          transitive-leq-Total-Order T c x b x≤b c≤x)
```

### If two closed intervals intersect, their intersection is their greatest lower bound

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  abstract
    is-greatest-binary-lower-bound-intersection-closed-interval-Total-Order :
      ([a,b] [c,d] : closed-interval-Total-Order T) →
      (H : intersect-closed-interval-Total-Order T [a,b] [c,d]) →
      is-greatest-binary-lower-bound-Poset
        ( poset-closed-interval-Total-Order T)
        ( [a,b])
        ( [c,d])
        ( intersection-closed-interval-Total-Order T [a,b] [c,d] H)
    pr1
      ( is-greatest-binary-lower-bound-intersection-closed-interval-Total-Order
        ((a , b) , a≤b) ((c , d) , c≤d) (a≤d , c≤b) ((e , f) , e≤f))
      ((a≤e , f≤b) , (c≤e , f≤d)) =
      ( leq-max-leq-both-Total-Order T a c e a≤e c≤e ,
        leq-min-leq-both-Total-Order T f b d f≤b f≤d)
    pr2
      ( is-greatest-binary-lower-bound-intersection-closed-interval-Total-Order
        ((a , b) , a≤b) ((c , d) , c≤d) (a≤d , c≤b) ((e , f) , e≤f))
      (maxac≤e , f≤minbd) =
      ( ( transitive-leq-Total-Order T a _ e
            ( maxac≤e)
            ( leq-left-max-Total-Order T a c) ,
          transitive-leq-Total-Order T f _ b
            ( leq-left-min-Total-Order T b d)
            ( f≤minbd)) ,
        ( transitive-leq-Total-Order T c _ e
            ( maxac≤e)
            ( leq-right-max-Total-Order T a c) ,
          transitive-leq-Total-Order T f _ d
            ( leq-right-min-Total-Order T b d)
            ( f≤minbd)))
```

### The span of closed intervals is their least upper bound

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

  abstract
    is-least-binary-upper-bound-span-closed-interval-Total-Order :
      ([a,b] [c,d] : closed-interval-Total-Order T) →
      is-least-binary-upper-bound-Poset
        ( poset-closed-interval-Total-Order T)
        ( [a,b])
        ( [c,d])
        ( span-closed-interval-Total-Order [a,b] [c,d])
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
