# Intersections of closed intervals in total orders

```agda
module order-theory.intersections-closed-intervals-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.intersections-subtypes
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.universe-levels

open import order-theory.closed-intervals-total-orders
open import order-theory.greatest-lower-bounds-posets
open import order-theory.poset-closed-intervals-total-orders
open import order-theory.total-orders
```

</details>

## Idea

In a [total order](order-theory.total-orders.md) `T`, two
[closed intervals](order-theory.closed-intervals-total-orders.md) in `T` [a, b]
and [c, d]
{{#concept "intersect" Disambiguation="closed intervals in a total order" Agda=intersect-closed-interval-Total-Order}}
if `a ≤ d` and `c ≤ b`.

If [a, b] and [c, d] intersect, their intersection is itself a closed interval.

## Definition

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
```

## Properties

### Intersection is reflexive

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  refl-intersect-closed-interval-Total-Order :
    ([a,b] : closed-interval-Total-Order T) →
    intersect-closed-interval-Total-Order T [a,b] [a,b]
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

### The intersection of two closed intervals is contained in both

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  abstract
    leq-left-intersection-closed-interval-Total-Order :
      ([a,b] [c,d] : closed-interval-Total-Order T) →
      (H : intersect-closed-interval-Total-Order T [a,b] [c,d]) →
      leq-closed-interval-Total-Order T
        ( intersection-closed-interval-Total-Order T [a,b] [c,d] H)
        ( [a,b])
    leq-left-intersection-closed-interval-Total-Order
      ((a , b) , _) ((c , d) , _) H =
      ( leq-left-max-Total-Order T a c ,
        leq-left-min-Total-Order T b d)

    leq-right-intersection-closed-interval-Total-Order :
      ([a,b] [c,d] : closed-interval-Total-Order T) →
      (H : intersect-closed-interval-Total-Order T [a,b] [c,d]) →
      leq-closed-interval-Total-Order T
        ( intersection-closed-interval-Total-Order T [a,b] [c,d] H)
        ( [c,d])
    leq-right-intersection-closed-interval-Total-Order
      ((a , b) , _) ((c , d) , _) H =
      ( leq-right-max-Total-Order T a c ,
        leq-right-min-Total-Order T b d)
```
