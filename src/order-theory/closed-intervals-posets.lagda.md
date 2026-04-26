# Closed intervals in posets

```agda
module order-theory.closed-intervals-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.images-subtypes
open import foundation.inhabited-subtypes
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.interval-subposets
open import order-theory.posets
```

</details>

## Idea

A
{{#concept "closed interval" disambiguation="in a poset" Agda=closed-interval-Poset}}
in a [poset](order-theory.posets.md) `P` is a [subtype](foundation.subtypes.md)
of `P` with elements `x` and `y` with `x ≤ y` such that the subtype contains
every element `z` such that `x ≤ z ∧ z ≤ y`. Note, in particular, that we thus
consider closed intervals to be inhabited by convention.

Any pair `x y` with `x ≤ y` induces a unique closed interval, so we can
equivalently characterize closed intervals in terms of such pairs.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  closed-interval-Poset : UU (l1 ⊔ l2)
  closed-interval-Poset =
    Σ (type-Poset X × type-Poset X) (λ (x , y) → leq-Poset X x y)

  lower-bound-closed-interval-Poset :
    closed-interval-Poset → type-Poset X
  lower-bound-closed-interval-Poset ((x , _) , _) = x

  upper-bound-closed-interval-Poset :
    closed-interval-Poset → type-Poset X
  upper-bound-closed-interval-Poset ((_ , y) , _) = y

  subtype-closed-interval-Poset :
    closed-interval-Poset → subtype l2 (type-Poset X)
  subtype-closed-interval-Poset ((x , y) , _) =
    is-in-interval-Poset X x y

  type-closed-interval-Poset :
    closed-interval-Poset → UU (l1 ⊔ l2)
  type-closed-interval-Poset [x,y] =
    type-subtype (subtype-closed-interval-Poset [x,y])

  is-in-closed-interval-Poset :
    closed-interval-Poset → type-Poset X → UU l2
  is-in-closed-interval-Poset [x,y] =
    is-in-subtype (subtype-closed-interval-Poset [x,y])
```

## Properties

### The endpoints of a closed interval are in the interval

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  abstract
    lower-bound-is-in-closed-interval-Poset :
      ([a,b] : closed-interval-Poset X) →
      is-in-closed-interval-Poset X [a,b]
        ( lower-bound-closed-interval-Poset X [a,b])
    lower-bound-is-in-closed-interval-Poset ((a , b) , a≤b) =
      ( refl-leq-Poset X a , a≤b)

    upper-bound-is-in-closed-interval-Poset :
      ([a,b] : closed-interval-Poset X) →
      is-in-closed-interval-Poset X [a,b]
        ( upper-bound-closed-interval-Poset X [a,b])
    upper-bound-is-in-closed-interval-Poset ((a , b) , a≤b) =
      ( a≤b , refl-leq-Poset X b)
```

### Closed intervals are inhabited

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2) ([x,y] : closed-interval-Poset X)
  where

  abstract
    is-inhabited-closed-interval-Poset :
      is-inhabited-subtype (subtype-closed-interval-Poset X [x,y])
    is-inhabited-closed-interval-Poset =
      unit-trunc-Prop
        ( lower-bound-closed-interval-Poset X [x,y] ,
          lower-bound-is-in-closed-interval-Poset X [x,y])
```

### Characterization of equality

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  abstract
    eq-closed-interval-Poset :
      ( [a,b] [c,d] : closed-interval-Poset X) →
      ( lower-bound-closed-interval-Poset X [a,b] ＝
        lower-bound-closed-interval-Poset X [c,d]) →
      ( upper-bound-closed-interval-Poset X [a,b] ＝
        upper-bound-closed-interval-Poset X [c,d]) →
      [a,b] ＝ [c,d]
    eq-closed-interval-Poset ((a , b) , _) ((c , d) , _) a=c b=d =
      eq-pair-Σ (eq-pair a=c b=d) (eq-type-Prop (leq-prop-Poset X _ _))

  set-closed-interval-Poset : Set (l1 ⊔ l2)
  set-closed-interval-Poset =
    set-subset
      ( product-Set (set-Poset X) (set-Poset X))
      ( ind-Σ (leq-prop-Poset X))
```

### The map from closed intervals to subtypes is injective

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  abstract
    is-injective-subtype-closed-interval-Poset :
      is-injective (subtype-closed-interval-Poset X)
    is-injective-subtype-closed-interval-Poset
      {(a , b) , a≤b} {(c , d) , c≤d} [a,b]=[c,d] =
        eq-closed-interval-Poset X _ _
          ( antisymmetric-leq-Poset X a c
            ( pr1
              ( backward-implication
                ( has-same-elements-eq-subtype _ _ [a,b]=[c,d] c)
                ( refl-leq-Poset X c , c≤d)))
            ( pr1
              ( forward-implication
                ( has-same-elements-eq-subtype _ _ [a,b]=[c,d] a)
                ( refl-leq-Poset X a , a≤b))))
          ( antisymmetric-leq-Poset X b d
            ( pr2
              ( forward-implication
                ( has-same-elements-eq-subtype _ _ [a,b]=[c,d] b)
                ( a≤b , refl-leq-Poset X b)))
            ( pr2
              ( backward-implication
                ( has-same-elements-eq-subtype _ _ [a,b]=[c,d] d)
                ( c≤d , refl-leq-Poset X d))))
```
