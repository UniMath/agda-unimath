# Closed intervals in total orders

```agda
module order-theory.closed-intervals-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.injective-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.universe-levels

open import order-theory.closed-intervals-posets
open import order-theory.posets
open import order-theory.total-orders
```

</details>

## Idea

A
{{#concept "closed interval" disambiguation="in a total order" Agda=closed-interval-Total-Order}}
in a [total order](order-theory.total-orders.md) `T` is a
[closed interval](order-theory.closed-intervals-posets.md) in the underlying
[poset](order-theory.posets.md).

## Definition

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2)
  where

  closed-interval-Total-Order : UU (l1 ⊔ l2)
  closed-interval-Total-Order =
    closed-interval-Poset (poset-Total-Order X)

  lower-bound-closed-interval-Total-Order :
    closed-interval-Total-Order → type-Total-Order X
  lower-bound-closed-interval-Total-Order ((x , _) , _) = x

  upper-bound-closed-interval-Total-Order :
    closed-interval-Total-Order → type-Total-Order X
  upper-bound-closed-interval-Total-Order ((_ , y) , _) = y

  subtype-closed-interval-Total-Order :
    closed-interval-Total-Order → subtype l2 (type-Total-Order X)
  subtype-closed-interval-Total-Order =
    subtype-closed-interval-Poset (poset-Total-Order X)

  type-closed-interval-Total-Order : closed-interval-Total-Order → UU (l1 ⊔ l2)
  type-closed-interval-Total-Order =
    type-closed-interval-Poset (poset-Total-Order X)

  is-in-closed-interval-Total-Order :
    closed-interval-Total-Order → type-Total-Order X → UU l2
  is-in-closed-interval-Total-Order =
    is-in-closed-interval-Poset (poset-Total-Order X)
```

## Properties

### The endpoints of a closed interval are in the interval

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2)
  where

  abstract
    lower-bound-is-in-closed-interval-Total-Order :
      ([a,b] : closed-interval-Total-Order X) →
      is-in-closed-interval-Total-Order X [a,b]
        ( lower-bound-closed-interval-Total-Order X [a,b])
    lower-bound-is-in-closed-interval-Total-Order =
      lower-bound-is-in-closed-interval-Poset (poset-Total-Order X)

    upper-bound-is-in-closed-interval-Total-Order :
      ([a,b] : closed-interval-Total-Order X) →
      is-in-closed-interval-Total-Order X [a,b]
        ( upper-bound-closed-interval-Total-Order X [a,b])
    upper-bound-is-in-closed-interval-Total-Order =
      upper-bound-is-in-closed-interval-Poset (poset-Total-Order X)
```

### Closed intervals are inhabited

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2)
  ([x,y] : closed-interval-Total-Order X)
  where

  abstract
    is-inhabited-closed-interval-Total-Order :
      is-inhabited-subtype (subtype-closed-interval-Total-Order X [x,y])
    is-inhabited-closed-interval-Total-Order =
      is-inhabited-closed-interval-Poset (poset-Total-Order X) [x,y]
```

### Characterization of equality

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2)
  where

  abstract
    eq-closed-interval-Total-Order :
      ( [a,b] [c,d] : closed-interval-Total-Order X) →
      ( lower-bound-closed-interval-Total-Order X [a,b] ＝
        lower-bound-closed-interval-Total-Order X [c,d]) →
      ( upper-bound-closed-interval-Total-Order X [a,b] ＝
        upper-bound-closed-interval-Total-Order X [c,d]) →
      [a,b] ＝ [c,d]
    eq-closed-interval-Total-Order =
      eq-closed-interval-Poset (poset-Total-Order X)

  set-closed-interval-Total-Order : Set (l1 ⊔ l2)
  set-closed-interval-Total-Order =
    set-closed-interval-Poset (poset-Total-Order X)
```

### The map from closed intervals to subtypes is injective

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2)
  where

  abstract
    is-injective-subtype-closed-interval-Total-Order :
      is-injective (subtype-closed-interval-Total-Order X)
    is-injective-subtype-closed-interval-Total-Order =
      is-injective-subtype-closed-interval-Poset (poset-Total-Order X)
```

### The property of a map of taking a closed interval to a closed interval

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Total-Order l1 l2) (Y : Total-Order l3 l4)
  (f : type-Total-Order X → type-Total-Order Y)
  where

  is-closed-interval-map-prop-Total-Order :
    ([a,b] : closed-interval-Total-Order X) →
    ([c,d] : closed-interval-Total-Order Y) →
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-closed-interval-map-prop-Total-Order =
    is-closed-interval-map-prop-Poset
      ( poset-Total-Order X)
      ( poset-Total-Order Y)
      ( f)

  is-closed-interval-map-Total-Order :
    ([a,b] : closed-interval-Total-Order X) →
    ([c,d] : closed-interval-Total-Order Y) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-closed-interval-map-Total-Order [a,b] [c,d] =
    type-Prop (is-closed-interval-map-prop-Total-Order [a,b] [c,d])
```

### Total orders can be divided along an element

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2)
  where

  divide-below-closed-interval-Total-Order :
    ([a,b] : closed-interval-Total-Order X) →
    (c : type-closed-interval-Total-Order X [a,b]) →
    closed-interval-Total-Order X
  divide-below-closed-interval-Total-Order ((a , b) , a≤b) (c , a≤c , c≤b) =
    ((a , c) , a≤c)

  divide-above-closed-interval-Total-Order :
    ([a,b] : closed-interval-Total-Order X) →
    (c : type-closed-interval-Total-Order X [a,b]) →
    closed-interval-Total-Order X
  divide-above-closed-interval-Total-Order ((a , b) , a≤b) (c , a≤c , c≤b) =
    ((c , b) , c≤b)

  abstract
    has-same-elements-divide-subtype-closed-interval-Total-Order :
      ([a,b] : closed-interval-Total-Order X) →
      (c : type-closed-interval-Total-Order X [a,b]) →
      has-same-elements-subtype
        ( union-subtype
          ( subtype-closed-interval-Total-Order X
            ( divide-below-closed-interval-Total-Order [a,b] c))
          ( subtype-closed-interval-Total-Order X
            ( divide-above-closed-interval-Total-Order [a,b] c)))
        ( subtype-closed-interval-Total-Order X [a,b])
    pr1
      ( has-same-elements-divide-subtype-closed-interval-Total-Order
        [a,b]@((a , b) , a≤b) (c , a≤c , c≤b) x) =
          elim-disjunction
            ( subtype-closed-interval-Total-Order X [a,b] x)
            ( λ (a≤x , x≤c) →
              ( a≤x , transitive-leq-Total-Order X x c b c≤b x≤c))
            ( λ (c≤x , x≤b) →
              ( transitive-leq-Total-Order X a c x c≤x a≤c , x≤b))
    pr2
      ( has-same-elements-divide-subtype-closed-interval-Total-Order
        [a,b]@((a , b) , a≤b) (c , a≤c , c≤b) x) (a≤x , x≤b) =
          map-disjunction
            ( λ x≤c → (a≤x , x≤c))
            ( λ c≤x → (c≤x , x≤b))
            ( is-total-Total-Order X x c)

    eq-divide-subtype-closed-interval-Total-Order :
      ([a,b] : closed-interval-Total-Order X) →
      (c : type-closed-interval-Total-Order X [a,b]) →
      union-subtype
        ( subtype-closed-interval-Total-Order X
          ( divide-below-closed-interval-Total-Order [a,b] c))
        ( subtype-closed-interval-Total-Order X
          ( divide-above-closed-interval-Total-Order [a,b] c)) ＝
      subtype-closed-interval-Total-Order X [a,b]
    eq-divide-subtype-closed-interval-Total-Order [a,b] c =
      eq-has-same-elements-subtype _ _
        ( has-same-elements-divide-subtype-closed-interval-Total-Order [a,b] c)
```

### The minimal interval covering two elements

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2) (a b : type-Total-Order X)
  where

  closed-interval-2-Total-Order : closed-interval-Total-Order X
  closed-interval-2-Total-Order =
    ( ( min-Total-Order X a b ,
        max-Total-Order X a b) ,
      min-leq-max-Total-Order X a b)
```

### Covering the minimal interval containing four elements

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2) (a b c d : type-Total-Order X)
  where

  closed-interval-4-Total-Order : closed-interval-Total-Order X
  closed-interval-4-Total-Order =
    ( ( min-Total-Order X (min-Total-Order X a b) (min-Total-Order X c d) ,
        max-Total-Order X (max-Total-Order X a b) (max-Total-Order X c d)) ,
      transitive-leq-Total-Order X _ _ _
        ( max-leq-leq-Total-Order X _ _ _ _
          ( min-leq-max-Total-Order X _ _)
          ( min-leq-max-Total-Order X _ _))
        ( min-leq-max-Total-Order X _ _))

  cover-closed-interval-4-Total-Order :
    subtype-closed-interval-Total-Order X
      ( closed-interval-4-Total-Order) ⊆
    union-subtype
      ( union-subtype
        ( subtype-closed-interval-Total-Order X
          ( closed-interval-2-Total-Order X a b))
        ( subtype-closed-interval-Total-Order X
          ( closed-interval-2-Total-Order X a c)))
      ( union-subtype
        ( subtype-closed-interval-Total-Order X
          ( closed-interval-2-Total-Order X b d))
        ( subtype-closed-interval-Total-Order X
          ( closed-interval-2-Total-Order X c d)))
  cover-closed-interval-4-Total-Order x x∈closed-4 =
    let
      motive =
        union-subtype
          ( union-subtype
            ( subtype-closed-interval-Total-Order X
              ( closed-interval-2-Total-Order X a b))
            ( subtype-closed-interval-Total-Order X
              ( closed-interval-2-Total-Order X a c)))
          ( union-subtype
            ( subtype-closed-interval-Total-Order X
              ( closed-interval-2-Total-Order X b d))
            ( subtype-closed-interval-Total-Order X
              ( closed-interval-2-Total-Order X c d)))
          ( x)
    in
      {!   !}
```
