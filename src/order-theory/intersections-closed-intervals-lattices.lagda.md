# Intersections of closed intervals in lattices

```agda
module order-theory.intersections-closed-intervals-lattices where
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

open import order-theory.closed-intervals-lattices
open import order-theory.greatest-lower-bounds-posets
open import order-theory.lattices
open import order-theory.poset-closed-intervals-lattices
```

</details>

## Idea

In a [total order](order-theory.total-orders.md) `L`, two
[closed intervals](order-theory.closed-intervals-total-orders.md) in `L`
`[a, b]` and `[c, d]`
{{#concept "intersect" Disambiguation="closed intervals in a total order" Agda=intersect-closed-interval-Lattice}}
if `a ≤ d` and `c ≤ b`.

If `[a, b]` and `[c, d]` intersect, their intersection is itself a closed
interval.

## Definition

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  intersect-prop-closed-interval-Lattice :
    Relation-Prop l2 (closed-interval-Lattice L)
  intersect-prop-closed-interval-Lattice ((a , b) , _) ((c , d) , _) =
    leq-prop-Lattice L a d ∧ leq-prop-Lattice L c b

  intersect-closed-interval-Lattice :
    Relation l2 (closed-interval-Lattice L)
  intersect-closed-interval-Lattice =
    type-Relation-Prop intersect-prop-closed-interval-Lattice
```

## Properties

### Intersection is reflexive

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  refl-intersect-closed-interval-Lattice :
    ([a,b] : closed-interval-Lattice L) →
    intersect-closed-interval-Lattice L [a,b] [a,b]
  refl-intersect-closed-interval-Lattice ((a , b) , a≤b) =
    ( a≤b , a≤b)
```

### If two closed intervals intersect, their intersection is a closed interval

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  intersection-closed-interval-Lattice :
    ([a,b] [c,d] : closed-interval-Lattice L) →
    intersect-closed-interval-Lattice L [a,b] [c,d] →
    closed-interval-Lattice L
  intersection-closed-interval-Lattice
    ((a , b) , a≤b) ((c , d) , c≤d) (a≤d , c≤b) =
    ( (join-Lattice L a c , meet-Lattice L b d) ,
      leq-meet-leq-both-Lattice
        ( L)
        ( join-Lattice L a c)
        ( b)
        ( d)
        ( leq-join-leq-both-Lattice L a c b a≤b c≤b)
        ( leq-join-leq-both-Lattice L a c d a≤d c≤d))

  abstract
    is-intersection-closed-interval-Lattice :
      ([a,b] [c,d] : closed-interval-Lattice L) →
      (H : intersect-closed-interval-Lattice L [a,b] [c,d]) →
      subtype-closed-interval-Lattice L
        ( intersection-closed-interval-Lattice [a,b] [c,d] H) ＝
      intersection-subtype
        ( subtype-closed-interval-Lattice L [a,b])
        ( subtype-closed-interval-Lattice L [c,d])
    is-intersection-closed-interval-Lattice
      ((a , b) , a≤b) ((c , d) , c≤d) (a≤d , c≤b) =
      eq-sim-subtype _ _
        ( ( λ x (maxac≤x , x≤minbd) →
            ( ( transitive-leq-Lattice L a _ x
                  ( maxac≤x)
                  ( leq-left-join-Lattice L a c) ,
                transitive-leq-Lattice L x _ b
                  ( leq-left-meet-Lattice L b d)
                  ( x≤minbd)) ,
              ( transitive-leq-Lattice L c _ x
                  ( maxac≤x)
                  ( leq-right-join-Lattice L a c) ,
                transitive-leq-Lattice L x _ d
                  ( leq-right-meet-Lattice L b d)
                  ( x≤minbd)))) ,
          ( λ x ((a≤x , x≤b) , (c≤x , x≤d)) →
            ( leq-join-leq-both-Lattice L a c x a≤x c≤x ,
              leq-meet-leq-both-Lattice L x b d x≤b x≤d)))

    intersect-closed-interval-intersect-subtype-Lattice :
      ([a,b] [c,d] : closed-interval-Lattice L) →
      intersect-subtype
        ( subtype-closed-interval-Lattice L [a,b])
        ( subtype-closed-interval-Lattice L [c,d]) →
      intersect-closed-interval-Lattice L [a,b] [c,d]
    intersect-closed-interval-intersect-subtype-Lattice
      [a,b]@((a , b) , a≤b) [c,d]@((c , d) , c≤d) ∃x =
      let
        open
          do-syntax-trunc-Prop
            ( intersect-prop-closed-interval-Lattice L [a,b] [c,d])
      in do
        (x , (a≤x , x≤b) , (c≤x , x≤d)) ← ∃x
        ( transitive-leq-Lattice L a x d x≤d a≤x ,
          transitive-leq-Lattice L c x b x≤b c≤x)
```

### If two closed intervals intersect, their intersection is their greatest lower bound

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  abstract
    is-greatest-binary-lower-bound-intersection-closed-interval-Lattice :
      ([a,b] [c,d] : closed-interval-Lattice L) →
      (H : intersect-closed-interval-Lattice L [a,b] [c,d]) →
      is-greatest-binary-lower-bound-Poset
        ( poset-closed-interval-Lattice L)
        ( [a,b])
        ( [c,d])
        ( intersection-closed-interval-Lattice L [a,b] [c,d] H)
    pr1
      ( is-greatest-binary-lower-bound-intersection-closed-interval-Lattice
        ((a , b) , a≤b) ((c , d) , c≤d) (a≤d , c≤b) ((e , f) , e≤f))
      ((a≤e , f≤b) , (c≤e , f≤d)) =
      ( leq-join-leq-both-Lattice L a c e a≤e c≤e ,
        leq-meet-leq-both-Lattice L f b d f≤b f≤d)
    pr2
      ( is-greatest-binary-lower-bound-intersection-closed-interval-Lattice
        ((a , b) , a≤b) ((c , d) , c≤d) (a≤d , c≤b) ((e , f) , e≤f))
      (maxac≤e , f≤minbd) =
      ( ( transitive-leq-Lattice L a _ e
            ( maxac≤e)
            ( leq-left-join-Lattice L a c) ,
          transitive-leq-Lattice L f _ b
            ( leq-left-meet-Lattice L b d)
            ( f≤minbd)) ,
        ( transitive-leq-Lattice L c _ e
            ( maxac≤e)
            ( leq-right-join-Lattice L a c) ,
          transitive-leq-Lattice L f _ d
            ( leq-right-meet-Lattice L b d)
            ( f≤minbd)))
```

### The intersection of two closed intervals is contained in both

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  abstract
    leq-left-intersection-closed-interval-Lattice :
      ([a,b] [c,d] : closed-interval-Lattice L) →
      (H : intersect-closed-interval-Lattice L [a,b] [c,d]) →
      leq-closed-interval-Lattice L
        ( intersection-closed-interval-Lattice L [a,b] [c,d] H)
        ( [a,b])
    leq-left-intersection-closed-interval-Lattice
      ((a , b) , _) ((c , d) , _) H =
      ( leq-left-join-Lattice L a c ,
        leq-left-meet-Lattice L b d)

    leq-right-intersection-closed-interval-Lattice :
      ([a,b] [c,d] : closed-interval-Lattice L) →
      (H : intersect-closed-interval-Lattice L [a,b] [c,d]) →
      leq-closed-interval-Lattice L
        ( intersection-closed-interval-Lattice L [a,b] [c,d] H)
        ( [c,d])
    leq-right-intersection-closed-interval-Lattice
      ((a , b) , _) ((c , d) , _) H =
      ( leq-right-join-Lattice L a c ,
        leq-right-meet-Lattice L b d)
```
