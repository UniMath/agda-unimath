# Order preserving maps between total orders

```agda
module order-theory.order-preserving-maps-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.disjunction
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
open import order-theory.total-orders
```

</details>

## Idea

A map `f : P → Q` between the underlying types of two
[total orders](order-theory.total-orders.md) is said to be
{{#concept "order preserving" WD="increasing function" WDID=Q3075182 Agda=hom-Total-Order Disambiguation="map between total orders"}}
if `x ≤ y` in `P` implies `f x ≤ f y` in `Q`.

## Definition

### Order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Total-Order l1 l2) (Q : Total-Order l3 l4)
  where

  preserves-order-prop-Total-Order :
    (type-Total-Order P → type-Total-Order Q) → Prop (l1 ⊔ l2 ⊔ l4)
  preserves-order-prop-Total-Order =
    preserves-order-prop-Poset (poset-Total-Order P) (poset-Total-Order Q)

  preserves-order-Total-Order :
    (type-Total-Order P → type-Total-Order Q) → UU (l1 ⊔ l2 ⊔ l4)
  preserves-order-Total-Order =
    preserves-order-Poset (poset-Total-Order P) (poset-Total-Order Q)

  is-prop-preserves-order-Total-Order :
    (f : type-Total-Order P → type-Total-Order Q) →
    is-prop (preserves-order-Total-Order f)
  is-prop-preserves-order-Total-Order =
    is-prop-preserves-order-Poset (poset-Total-Order P) (poset-Total-Order Q)

  hom-set-Total-Order : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-set-Total-Order =
    set-subset
      ( function-Set (type-Total-Order P) (set-Total-Order Q))
      ( preserves-order-prop-Total-Order)

  hom-Total-Order : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Total-Order = type-Set hom-set-Total-Order

  map-hom-Total-Order :
    hom-Total-Order → type-Total-Order P → type-Total-Order Q
  map-hom-Total-Order =
    map-hom-Poset (poset-Total-Order P) (poset-Total-Order Q)

  preserves-order-hom-Total-Order :
    (f : hom-Total-Order) → preserves-order-Total-Order (map-hom-Total-Order f)
  preserves-order-hom-Total-Order =
    preserves-order-hom-Poset (poset-Total-Order P) (poset-Total-Order Q)
```

## Properties

### Order-preserving maps distribute over the minimum operation

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Total-Order l1 l2) (Q : Total-Order l3 l4)
  (f : hom-Total-Order P Q)
  where

  abstract
    distributive-map-hom-min-Total-Order :
      (x y : type-Total-Order P) →
      map-hom-Total-Order P Q f (min-Total-Order P x y) ＝
      min-Total-Order Q
        ( map-hom-Total-Order P Q f x)
        ( map-hom-Total-Order P Q f y)
    distributive-map-hom-min-Total-Order x y =
      elim-disjunction
        ( Id-Prop
          ( set-Total-Order Q)
          ( map-hom-Total-Order P Q f (min-Total-Order P x y))
          ( min-Total-Order Q
            ( map-hom-Total-Order P Q f x)
            ( map-hom-Total-Order P Q f y)))
        ( λ x≤y →
          equational-reasoning
            map-hom-Total-Order P Q f (min-Total-Order P x y)
            ＝ map-hom-Total-Order P Q f x
              by
                ap
                  ( map-hom-Total-Order P Q f)
                  ( left-leq-right-min-Total-Order P x y x≤y)
            ＝
              min-Total-Order Q
                ( map-hom-Total-Order P Q f x)
                ( map-hom-Total-Order P Q f y)
              by
                inv
                  ( left-leq-right-min-Total-Order Q _ _
                    ( preserves-order-hom-Total-Order P Q f x y x≤y)))
        ( λ y≤x →
          equational-reasoning
            map-hom-Total-Order P Q f (min-Total-Order P x y)
            ＝ map-hom-Total-Order P Q f y
              by
                ap
                  ( map-hom-Total-Order P Q f)
                  ( right-leq-left-min-Total-Order P x y y≤x)
            ＝
              min-Total-Order Q
                ( map-hom-Total-Order P Q f x)
                ( map-hom-Total-Order P Q f y)
              by
                inv
                  ( right-leq-left-min-Total-Order Q _ _
                    ( preserves-order-hom-Total-Order P Q f y x y≤x)))
        ( is-total-Total-Order P x y)
```

### Order-preserving maps distribute over the maximum operation

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Total-Order l1 l2) (Q : Total-Order l3 l4)
  (f : hom-Total-Order P Q)
  where

  abstract
    distributive-map-hom-max-Total-Order :
      (x y : type-Total-Order P) →
      map-hom-Total-Order P Q f (max-Total-Order P x y) ＝
      max-Total-Order Q
        ( map-hom-Total-Order P Q f x)
        ( map-hom-Total-Order P Q f y)
    distributive-map-hom-max-Total-Order x y =
      elim-disjunction
        ( Id-Prop
          ( set-Total-Order Q)
          ( map-hom-Total-Order P Q f (max-Total-Order P x y))
          ( max-Total-Order Q
            ( map-hom-Total-Order P Q f x)
            ( map-hom-Total-Order P Q f y)))
        ( λ x≤y →
          equational-reasoning
            map-hom-Total-Order P Q f (max-Total-Order P x y)
            ＝ map-hom-Total-Order P Q f y
              by
                ap
                  ( map-hom-Total-Order P Q f)
                  ( left-leq-right-max-Total-Order P x y x≤y)
            ＝
              max-Total-Order Q
                ( map-hom-Total-Order P Q f x)
                ( map-hom-Total-Order P Q f y)
              by
                inv
                  ( left-leq-right-max-Total-Order Q _ _
                    ( preserves-order-hom-Total-Order P Q f x y x≤y)))
        ( λ y≤x →
          equational-reasoning
            map-hom-Total-Order P Q f (max-Total-Order P x y)
            ＝ map-hom-Total-Order P Q f x
              by
                ap
                  ( map-hom-Total-Order P Q f)
                  ( right-leq-left-max-Total-Order P x y y≤x)
            ＝
              max-Total-Order Q
                ( map-hom-Total-Order P Q f x)
                ( map-hom-Total-Order P Q f y)
              by
                inv
                  ( right-leq-left-max-Total-Order Q _ _
                    ( preserves-order-hom-Total-Order P Q f y x y≤x)))
        ( is-total-Total-Order P x y)
```
