# Inhabited closed intervals in total orders

```agda
module order-theory.closed-intervals-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.function-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.injective-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
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
in a [total order](order-theory.total-orders.md) `X` is a
[subtype](foundation.subtypes.md) of `X` with elements `x` and `y` with `x ≤ y`
such that the subtype contains every element `z` such that `x ≤ z ∧ z ≤ y`. (We
choose the convention of not considering the empty subtype to be a closed
interval.)

Equivalently, a closed interval is a total order is a
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

  type-closed-interval-Total-Order :
    closed-interval-Total-Order → UU (l1 ⊔ l2)
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
      is-inhabited-subtype
        ( subtype-closed-interval-Total-Order X [x,y])
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

### Total orders can be divided along an element

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2)
  where

  divide-below-closed-interval-Total-Order :
    ([a,b] : closed-interval-Total-Order X) →
    (c : type-closed-interval-Total-Order X [a,b]) →
    closed-interval-Total-Order X
  divide-below-closed-interval-Total-Order
    ((a , b) , a≤b) (c , a≤c , c≤b) =
    ((a , c) , a≤c)

  divide-above-closed-interval-Total-Order :
    ([a,b] : closed-interval-Total-Order X) →
    (c : type-closed-interval-Total-Order X [a,b]) →
    closed-interval-Total-Order X
  divide-above-closed-interval-Total-Order
    ((a , b) , a≤b) (c , a≤c , c≤b) =
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
        ( has-same-elements-divide-subtype-closed-interval-Total-Order
          ( [a,b])
          ( c))
```

### The minimal interval covering two elements

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2) (a b : type-Total-Order X)
  where

  minimal-closed-interval-cover-of-two-elements-Total-Order :
    closed-interval-Total-Order X
  minimal-closed-interval-cover-of-two-elements-Total-Order =
    ( ( min-Total-Order X a b ,
        max-Total-Order X a b) ,
      min-leq-max-Total-Order X a b)
```

### Covering the minimal interval containing four elements

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2) (a b c d : type-Total-Order X)
  where

  minimal-closed-interval-cover-of-four-elements-Total-Order :
    closed-interval-Total-Order X
  minimal-closed-interval-cover-of-four-elements-Total-Order =
    ( ( min-Total-Order X (min-Total-Order X a b) (min-Total-Order X c d) ,
        max-Total-Order X (max-Total-Order X a b) (max-Total-Order X c d)) ,
      transitive-leq-Total-Order X _ _ _
        ( max-leq-leq-Total-Order X _ _ _ _
          ( min-leq-max-Total-Order X _ _)
          ( min-leq-max-Total-Order X _ _))
        ( min-leq-max-Total-Order X _ _))

  abstract
    cover-closed-interval-cover-of-four-elements-first-is-smallest-Total-Order :
      leq-Total-Order X a b → leq-Total-Order X a c → leq-Total-Order X a d →
      subtype-closed-interval-Total-Order X
        ( minimal-closed-interval-cover-of-four-elements-Total-Order) ⊆
      union-subtype
        ( union-subtype
          ( subtype-closed-interval-Total-Order X
            ( minimal-closed-interval-cover-of-two-elements-Total-Order X a b))
          ( subtype-closed-interval-Total-Order X
            ( minimal-closed-interval-cover-of-two-elements-Total-Order X a c)))
        ( subtype-closed-interval-Total-Order X
          ( minimal-closed-interval-cover-of-two-elements-Total-Order X b d))
    cover-closed-interval-cover-of-four-elements-first-is-smallest-Total-Order
      a≤b a≤c a≤d x (min≤x , x≤max) =
      let
        motive =
          union-subtype
            ( union-subtype
              ( subtype-closed-interval-Total-Order X
                ( minimal-closed-interval-cover-of-two-elements-Total-Order
                  ( X)
                  ( a)
                  ( b)))
              ( subtype-closed-interval-Total-Order X
                ( minimal-closed-interval-cover-of-two-elements-Total-Order
                  ( X)
                  ( a)
                  ( c))))
            ( subtype-closed-interval-Total-Order X
              ( minimal-closed-interval-cover-of-two-elements-Total-Order
                ( X)
                ( b)
                ( d)))
            ( x)
        minab≤x =
          tr
            ( λ y → leq-Total-Order X y x)
            ( left-leq-right-min-Total-Order X _ _
              ( inv-tr
                ( λ z → leq-Total-Order X z (min-Total-Order X c d))
                ( left-leq-right-min-Total-Order X a b a≤b)
                ( leq-min-leq-both-Total-Order X a c d a≤c a≤d)))
            ( min≤x)
        minac≤x =
          tr
            ( λ y → leq-Total-Order X y x)
            ( left-leq-right-min-Total-Order X a b a≤b ∙
              inv (left-leq-right-min-Total-Order X a c a≤c))
            ( minab≤x)
      in
        elim-disjunction
          ( motive)
          ( elim-disjunction
            ( motive)
            ( λ max=a →
              inl-disjunction
                ( inl-disjunction
                  ( minab≤x ,
                    transitive-leq-Total-Order X x a (max-Total-Order X a b)
                      ( leq-left-max-Total-Order X _ _)
                      ( tr (leq-Total-Order X x) max=a x≤max))))
            ( λ max=b →
              inl-disjunction
                ( inl-disjunction
                  ( minab≤x ,
                    tr
                      ( leq-Total-Order X x)
                      ( max=b ∙ inv (left-leq-right-max-Total-Order X a b a≤b))
                      ( x≤max)))))
          ( elim-disjunction
            ( motive)
            ( λ max=c →
              inl-disjunction
                ( inr-disjunction
                  ( minac≤x ,
                    tr
                      ( leq-Total-Order X x)
                      ( max=c ∙ inv (left-leq-right-max-Total-Order X a c a≤c))
                      ( x≤max))))
            ( λ max=d →
              elim-disjunction motive
                ( λ b≤x →
                  inr-disjunction
                    ( transitive-leq-Total-Order X (min-Total-Order X b d) b x
                        ( b≤x)
                        ( leq-left-min-Total-Order X b d) ,
                      transitive-leq-Total-Order X x d (max-Total-Order X b d)
                        ( leq-right-max-Total-Order X b d)
                        ( tr (leq-Total-Order X x) max=d x≤max)))
                ( λ x≤b →
                  inl-disjunction
                    ( inl-disjunction
                      ( minab≤x ,
                        inv-tr
                          ( leq-Total-Order X x)
                          ( left-leq-right-max-Total-Order X a b a≤b)
                          ( x≤b))))
                ( is-total-Total-Order X b x)))
          ( eq-one-of-four-max-Total-Order X a b c d)

module _
  {l1 l2 : Level} (X : Total-Order l1 l2) (a b c d : type-Total-Order X)
  where

  abstract
    cover-minimal-closed-interval-cover-of-four-elements-Total-Order :
      subtype-closed-interval-Total-Order X
        ( minimal-closed-interval-cover-of-four-elements-Total-Order X
          ( a)
          ( b)
          ( c)
          ( d)) ⊆
      union-subtype
        ( union-subtype
          ( subtype-closed-interval-Total-Order X
            ( minimal-closed-interval-cover-of-two-elements-Total-Order X a b))
          ( subtype-closed-interval-Total-Order X
            ( minimal-closed-interval-cover-of-two-elements-Total-Order X a c)))
        ( union-subtype
          ( subtype-closed-interval-Total-Order X
            ( minimal-closed-interval-cover-of-two-elements-Total-Order X b d))
          ( subtype-closed-interval-Total-Order X
            ( minimal-closed-interval-cover-of-two-elements-Total-Order X c d)))
    cover-minimal-closed-interval-cover-of-four-elements-Total-Order
      x x∈closed-4@(min≤x , x≤max) =
      let
        _≤_ = leq-Total-Order X
        commutative-min = commutative-min-Total-Order X
        commutative-max = commutative-max-Total-Order X
        min = min-Total-Order X
        max = max-Total-Order X
        motive =
          union-subtype
            ( union-subtype
              ( subtype-closed-interval-Total-Order X
                ( minimal-closed-interval-cover-of-two-elements-Total-Order
                  ( X)
                  ( a)
                  ( b)))
              ( subtype-closed-interval-Total-Order X
                ( minimal-closed-interval-cover-of-two-elements-Total-Order
                  ( X)
                  ( a)
                  ( c))))
            ( union-subtype
              ( subtype-closed-interval-Total-Order X
                ( minimal-closed-interval-cover-of-two-elements-Total-Order
                  ( X)
                  ( b)
                  ( d)))
              ( subtype-closed-interval-Total-Order X
                ( minimal-closed-interval-cover-of-two-elements-Total-Order
                  ( X)
                  ( c)
                  ( d))))
            ( x)
        min≤a =
          transitive-leq-Total-Order X
            ( min (min a b) (min c d))
            ( min a b)
            ( a)
            ( leq-left-min-Total-Order X _ _)
            ( leq-left-min-Total-Order X _ _)
        min≤b =
          transitive-leq-Total-Order X
            ( min (min a b) (min c d))
            ( min a b)
            ( b)
            ( leq-right-min-Total-Order X _ _)
            ( leq-left-min-Total-Order X _ _)
        min≤c =
          transitive-leq-Total-Order X
            ( min (min a b) (min c d))
            ( min c d)
            ( c)
            ( leq-left-min-Total-Order X _ _)
            ( leq-right-min-Total-Order X _ _)
        min≤d =
          transitive-leq-Total-Order X
            ( min (min a b) (min c d))
            ( min c d)
            ( d)
            ( leq-right-min-Total-Order X _ _)
            ( leq-right-min-Total-Order X _ _)
      in
        elim-disjunction motive
          ( elim-disjunction motive
            ( λ min=a →
              map-disjunction
                ( id)
                ( inl-disjunction)
                ( cover-closed-interval-cover-of-four-elements-first-is-smallest-Total-Order
                  ( X)
                  ( a)
                  ( b)
                  ( c)
                  ( d)
                  ( tr (_≤ b) min=a min≤b)
                  ( tr (_≤ c) min=a min≤c)
                  ( tr (_≤ d) min=a min≤d)
                  ( x)
                  ( x∈closed-4)))
            ( λ min=b →
              elim-disjunction motive
                ( elim-disjunction motive
                  ( λ (minba≤x , x≤maxba) →
                    inl-disjunction
                      ( inl-disjunction
                        ( tr (_≤ x) (commutative-min b a) minba≤x ,
                          tr (x ≤_) (commutative-max b a) x≤maxba)))
                  ( inr-disjunction ∘ inl-disjunction))
                ( inl-disjunction ∘ inr-disjunction)
                ( cover-closed-interval-cover-of-four-elements-first-is-smallest-Total-Order
                  ( X)
                  ( b)
                  ( a)
                  ( d)
                  ( c)
                  ( tr (_≤ a) min=b min≤a)
                  ( tr (_≤ d) min=b min≤d)
                  ( tr (_≤ c) min=b min≤c)
                  ( x)
                  ( transitive-leq-Total-Order X _ b x
                    ( tr (_≤ x) min=b min≤x)
                    ( transitive-leq-Total-Order X
                      ( min (min b a) (min d c)) (min b a) b
                        ( leq-left-min-Total-Order X _ _)
                        ( leq-left-min-Total-Order X _ _)) ,
                    tr
                      ( x ≤_)
                      ( ap-binary max
                        ( commutative-max _ _)
                        ( commutative-max _ _))
                      ( x≤max)))))
          ( elim-disjunction motive
            ( λ min=c →
              elim-disjunction motive
                ( elim-disjunction motive
                  ( λ (minca≤x , x≤maxca) →
                    inl-disjunction
                      ( inr-disjunction
                        ( tr (_≤ x) (commutative-min c a) minca≤x ,
                          tr (x ≤_) (commutative-max c a) x≤maxca)))
                  ( inr-disjunction ∘ inr-disjunction))
                ( inl-disjunction ∘ inl-disjunction)
                ( cover-closed-interval-cover-of-four-elements-first-is-smallest-Total-Order
                  ( X)
                  ( c)
                  ( a)
                  ( d)
                  ( b)
                  ( tr (_≤ a) min=c min≤a)
                  ( tr (_≤ d) min=c min≤d)
                  ( tr (_≤ b) min=c min≤b)
                  ( x)
                  ( tr
                      ( _≤ x)
                      ( interchange-law-min-Total-Order X a b c d ∙
                        ap-binary min
                          ( commutative-min _ _)
                          ( commutative-min _ _))
                      ( min≤x) ,
                    tr
                      ( x ≤_)
                      ( interchange-law-max-Total-Order X a b c d ∙
                        ap-binary max
                          ( commutative-max _ _)
                          ( commutative-max _ _))
                      ( x≤max))))
            ( λ min=d →
              elim-disjunction motive
                ( elim-disjunction motive
                  ( λ (mindb≤x , x≤maxdb) →
                    inr-disjunction
                      ( inl-disjunction
                        ( tr (_≤ x) (commutative-min _ _) mindb≤x ,
                          tr (x ≤_) (commutative-max _ _) x≤maxdb)))
                  ( λ (mindc≤x , x≤maxdc) →
                    inr-disjunction
                      ( inr-disjunction
                        ( tr (_≤ x) (commutative-min _ _) mindc≤x ,
                          tr (x ≤_) (commutative-max _ _) x≤maxdc))))
                ( λ (minba≤x , x≤maxba) →
                  inl-disjunction
                    ( inl-disjunction
                      ( tr (_≤ x) (commutative-min _ _) minba≤x ,
                        tr (x ≤_) (commutative-max _ _) x≤maxba)))
                ( cover-closed-interval-cover-of-four-elements-first-is-smallest-Total-Order
                  ( X)
                  ( d)
                  ( b)
                  ( c)
                  ( a)
                  ( tr (_≤ b) min=d min≤b)
                  ( tr (_≤ c) min=d min≤c)
                  ( tr (_≤ a) min=d min≤a)
                  ( x)
                  ( tr
                      ( _≤ x)
                      ( interchange-law-min-Total-Order X a b c d ∙
                        ap-binary min
                          ( commutative-min _ _)
                          ( commutative-min _ _) ∙
                        commutative-min _ _)
                      ( min≤x) ,
                    tr
                      ( x ≤_)
                      ( interchange-law-max-Total-Order X a b c d ∙
                        ap-binary max
                          ( commutative-max _ _)
                          ( commutative-max _ _) ∙
                        commutative-max _ _)
                      ( x≤max)))))
          ( eq-one-of-four-min-Total-Order X a b c d)
```
