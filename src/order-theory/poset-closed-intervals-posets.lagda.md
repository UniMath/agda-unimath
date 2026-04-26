# The poset of closed intervals in posets

```agda
module order-theory.poset-closed-intervals-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.closed-intervals-posets
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

In a [poset](order-theory.posets.md) `P`, the type of
[closed intervals](order-theory.closed-intervals-posets.md) in `P` itself forms
a poset, with inequality defined by containment of the corresponding subtypes.
Equivalently, `[a,b] ≤ [c,d]` if `c ≤ a` and `b ≤ d`.

## Definition

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  leq-prop-closed-interval-Poset : Relation-Prop l2 (closed-interval-Poset P)
  leq-prop-closed-interval-Poset ((a , b) , a≤b) ((c , d) , c≤d) =
    leq-prop-Poset P c a ∧ leq-prop-Poset P b d

  leq-closed-interval-Poset : Relation l2 (closed-interval-Poset P)
  leq-closed-interval-Poset = type-Relation-Prop leq-prop-closed-interval-Poset
```

## Properties

### Containment is a preorder

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  abstract
    refl-leq-closed-interval-Poset : is-reflexive (leq-closed-interval-Poset P)
    refl-leq-closed-interval-Poset ((a , b) , _) =
      ( refl-leq-Poset P a , refl-leq-Poset P b)

    transitive-leq-closed-interval-Poset :
      is-transitive (leq-closed-interval-Poset P)
    transitive-leq-closed-interval-Poset
      ((a , b) , _) ((c , d) , _) ((e , f) , _) (e≤c , d≤f) (c≤a , b≤d) =
      ( transitive-leq-Poset P e c a c≤a e≤c ,
        transitive-leq-Poset P b d f d≤f b≤d)

  is-preorder-leq-closed-interval-Poset :
    is-preorder-Relation-Prop (leq-prop-closed-interval-Poset P)
  is-preorder-leq-closed-interval-Poset =
    ( refl-leq-closed-interval-Poset ,
      transitive-leq-closed-interval-Poset)

  preorder-closed-interval-Poset : Preorder (l1 ⊔ l2) l2
  preorder-closed-interval-Poset =
    ( closed-interval-Poset P ,
      leq-prop-closed-interval-Poset P ,
      is-preorder-leq-closed-interval-Poset)
```

### Containment is a partial order

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  abstract
    antisymmetric-leq-closed-interval-Poset :
      is-antisymmetric (leq-closed-interval-Poset P)
    antisymmetric-leq-closed-interval-Poset
      ((a , b) , a≤b) ((c , d) , c≤d) (c≤a , b≤d) (a≤c , d≤b) =
      eq-closed-interval-Poset P _ _
        ( antisymmetric-leq-Poset P a c a≤c c≤a)
        ( antisymmetric-leq-Poset P b d b≤d d≤b)

  poset-closed-interval-Poset : Poset (l1 ⊔ l2) l2
  poset-closed-interval-Poset =
    ( preorder-closed-interval-Poset P ,
      antisymmetric-leq-closed-interval-Poset)
```

### Containment of closed intervals is equivalent to containment of subtypes

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  abstract
    leq-subtype-leq-closed-interval-Poset :
      ([a,b] [c,d] : closed-interval-Poset P) →
      leq-closed-interval-Poset P [a,b] [c,d] →
      ( subtype-closed-interval-Poset P [a,b] ⊆
        subtype-closed-interval-Poset P [c,d])
    leq-subtype-leq-closed-interval-Poset
      ((a , b) , a≤b) ((c , d) , c≤d) (c≤a , b≤d) x (a≤x , x≤b) =
      ( transitive-leq-Poset P c a x a≤x c≤a ,
        transitive-leq-Poset P x b d b≤d x≤b)

    leq-closed-interval-leq-subtype-Poset :
      ([a,b] [c,d] : closed-interval-Poset P) →
      ( subtype-closed-interval-Poset P [a,b] ⊆
        subtype-closed-interval-Poset P [c,d]) →
      leq-closed-interval-Poset P [a,b] [c,d]
    leq-closed-interval-leq-subtype-Poset
      [a,b]@((a , b) , a≤b) [c,d]@((c , d) , c≤d) H =
      ( pr1 (H a (lower-bound-is-in-closed-interval-Poset P [a,b])) ,
        pr2 (H b (upper-bound-is-in-closed-interval-Poset P [a,b])))

    leq-subtype-iff-leq-closed-interval-Poset :
      ([a,b] [c,d] : closed-interval-Poset P) →
      ( leq-closed-interval-Poset P [a,b] [c,d] ↔
        ( subtype-closed-interval-Poset P [a,b] ⊆
          subtype-closed-interval-Poset P [c,d]))
    leq-subtype-iff-leq-closed-interval-Poset [a,b] [c,d] =
      ( leq-subtype-leq-closed-interval-Poset [a,b] [c,d] ,
        leq-closed-interval-leq-subtype-Poset [a,b] [c,d])
```
