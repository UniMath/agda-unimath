# Intersections of closed intervals of rational numbers

```agda
module elementary-number-theory.intersections-closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.poset-closed-intervals-rational-numbers

open import foundation.binary-relations
open import foundation.identity-types
open import foundation.intersections-subtypes
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-posets
open import order-theory.intersections-closed-intervals-total-orders
```

</details>

## Idea

Two
[closed intervals](elementary-number-theory.closed-intervals-rational-numbers.md)
`[a, b]` and `[c, d]` of
[rational numbers](elementary-number-theory.rational-numbers.md)
{{#concept "intersect" Disambiguation="closed intervals of rational numbers"}}
if `a ≤ d` and `c ≤ b`.

If `[a, b]` and `[c, d]` intersect, their intersection is itself a closed
interval.

## Definition

```agda
intersect-prop-closed-interval-ℚ : Relation-Prop lzero closed-interval-ℚ
intersect-prop-closed-interval-ℚ =
  intersect-prop-closed-interval-Total-Order ℚ-Total-Order

intersect-closed-interval-ℚ : Relation lzero closed-interval-ℚ
intersect-closed-interval-ℚ =
  intersect-closed-interval-Total-Order ℚ-Total-Order
```

## Properties

### Intersection is reflexive

```agda
refl-intersect-closed-interval-ℚ : is-reflexive intersect-closed-interval-ℚ
refl-intersect-closed-interval-ℚ =
  refl-intersect-closed-interval-Total-Order ℚ-Total-Order
```

### If two intervals intersect, their intersection is a closed interval

```agda
intersection-closed-interval-ℚ :
  ([a,b] [c,d] : closed-interval-ℚ) → intersect-closed-interval-ℚ [a,b] [c,d] →
  closed-interval-ℚ
intersection-closed-interval-ℚ =
  intersection-closed-interval-Total-Order ℚ-Total-Order

is-intersection-closed-interval-ℚ :
  ([a,b] [c,d] : closed-interval-ℚ) →
  (H : intersect-closed-interval-ℚ [a,b] [c,d]) →
  subtype-closed-interval-ℚ
    ( intersection-closed-interval-ℚ [a,b] [c,d] H) ＝
  intersection-subtype
    ( subtype-closed-interval-ℚ [a,b])
    ( subtype-closed-interval-ℚ [c,d])
is-intersection-closed-interval-ℚ =
  is-intersection-closed-interval-Total-Order ℚ-Total-Order

intersect-closed-interval-intersect-subtype-ℚ :
  ([a,b] [c,d] : closed-interval-ℚ) →
  intersect-subtype
    ( subtype-closed-interval-ℚ [a,b])
    ( subtype-closed-interval-ℚ [c,d]) →
  intersect-closed-interval-ℚ [a,b] [c,d]
intersect-closed-interval-intersect-subtype-ℚ =
  intersect-closed-interval-intersect-subtype-Total-Order ℚ-Total-Order
```

### If two closed intervals intersect, their intersection is their greatest lower bound

```agda
is-greatest-binary-lower-bound-intersection-closed-interval-ℚ :
  ([a,b] [c,d] : closed-interval-ℚ) →
  (H : intersect-closed-interval-ℚ [a,b] [c,d]) →
  is-greatest-binary-lower-bound-Poset
    ( poset-closed-interval-ℚ)
    ( [a,b])
    ( [c,d])
    ( intersection-closed-interval-ℚ [a,b] [c,d] H)
is-greatest-binary-lower-bound-intersection-closed-interval-ℚ =
  is-greatest-binary-lower-bound-intersection-closed-interval-Total-Order
    ( ℚ-Total-Order)
```

### If two closed intervals intersect, their intersection is contained in both

```agda
abstract
  leq-left-intersection-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (H : intersect-closed-interval-ℚ [a,b] [c,d]) →
    leq-closed-interval-ℚ (intersection-closed-interval-ℚ [a,b] [c,d] H) [a,b]
  leq-left-intersection-closed-interval-ℚ =
    leq-left-intersection-closed-interval-Total-Order ℚ-Total-Order

  leq-right-intersection-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (H : intersect-closed-interval-ℚ [a,b] [c,d]) →
    leq-closed-interval-ℚ (intersection-closed-interval-ℚ [a,b] [c,d] H) [c,d]
  leq-right-intersection-closed-interval-ℚ =
    leq-right-intersection-closed-interval-Total-Order ℚ-Total-Order
```
