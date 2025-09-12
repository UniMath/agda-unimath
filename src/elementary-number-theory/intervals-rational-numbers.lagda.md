# Intervals in the rational numbers

```agda
module elementary-number-theory.intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.closed-intervals-posets
open import order-theory.decidable-total-orders
```

</details>

## Idea

An interval in the rational numbers is a
[closed interval](order-theory.closed-intervals-posets.md) in the
[poset](elementary-number-theory.inequality-rational-numbers.md) of
[rational numbers](elementary-number-theory.rational-numbers.md).

## Definition

```agda
interval-ℚ : UU lzero
interval-ℚ = closed-interval-Poset ℚ-Poset

lower-bound-interval-ℚ : interval-ℚ → ℚ
lower-bound-interval-ℚ = lower-bound-closed-interval-Poset ℚ-Poset

upper-bound-interval-ℚ : interval-ℚ → ℚ
upper-bound-interval-ℚ = upper-bound-closed-interval-Poset ℚ-Poset

subtype-interval-ℚ : interval-ℚ → subtype lzero ℚ
subtype-interval-ℚ = subtype-closed-interval-Poset ℚ-Poset

is-in-interval-ℚ : interval-ℚ → ℚ → UU lzero
is-in-interval-ℚ [a,b] = is-in-subtype (subtype-interval-ℚ [a,b])

is-closed-interval-map-prop-ℚ :
  (ℚ → ℚ) → interval-ℚ → interval-ℚ → Prop lzero
is-closed-interval-map-prop-ℚ =
  is-closed-interval-map-prop-Poset ℚ-Poset ℚ-Poset

is-below-prop-interval-ℚ : interval-ℚ → subtype lzero ℚ
is-below-prop-interval-ℚ ((a , _) , _) b = le-ℚ-Prop b a

is-above-prop-interval-ℚ : interval-ℚ → subtype lzero ℚ
is-above-prop-interval-ℚ ((_ , a) , _) b = le-ℚ-Prop a b

nonnegative-width-interval-ℚ : interval-ℚ → ℚ⁰⁺
nonnegative-width-interval-ℚ ((a , b) , a≤b) = nonnegative-diff-leq-ℚ a b a≤b

width-interval-ℚ : interval-ℚ → ℚ
width-interval-ℚ [a,b] = rational-ℚ⁰⁺ (nonnegative-width-interval-ℚ [a,b])

is-injective-subtype-interval-ℚ :
  is-injective subtype-interval-ℚ
is-injective-subtype-interval-ℚ =
  is-injective-subtype-closed-interval-Poset ℚ-Poset
```

### Important ranges

```agda
zero-zero-interval-ℚ : interval-ℚ
zero-zero-interval-ℚ = ((zero-ℚ , zero-ℚ) , refl-leq-ℚ zero-ℚ)

one-one-interval-ℚ : interval-ℚ
one-one-interval-ℚ = ((one-ℚ , one-ℚ) , refl-leq-ℚ one-ℚ)
```

## Properties

### Characterization of equality

```agda
eq-interval-ℚ :
  ([a,b] [c,d] : interval-ℚ) →
  lower-bound-interval-ℚ [a,b] ＝ lower-bound-interval-ℚ [c,d] →
  upper-bound-interval-ℚ [a,b] ＝ upper-bound-interval-ℚ [c,d] →
  [a,b] ＝ [c,d]
eq-interval-ℚ = eq-closed-interval-Poset ℚ-Poset

set-interval-ℚ : Set lzero
set-interval-ℚ = set-closed-interval-Poset ℚ-Poset
```

### Unordered intervals

```agda
unordered-interval-ℚ : ℚ → ℚ → interval-ℚ
unordered-interval-ℚ a b =
  ( (min-ℚ a b , max-ℚ a b) ,
    min-leq-max-Decidable-Total-Order ℚ-Decidable-Total-Order a b)

abstract
  unordered-interval-leq-ℚ :
    (p q : ℚ) → (p≤q : leq-ℚ p q) → unordered-interval-ℚ p q ＝ ((p , q) , p≤q)
  unordered-interval-leq-ℚ p q p≤q =
    eq-interval-ℚ _ _
      (left-leq-right-min-ℚ p q p≤q)
      (left-leq-right-max-ℚ p q p≤q)

  unordered-interval-leq-ℚ' :
    (p q : ℚ) → (q≤p : leq-ℚ q p) → unordered-interval-ℚ p q ＝ ((q , p) , q≤p)
  unordered-interval-leq-ℚ' p q q≤p =
    eq-interval-ℚ _ _
      (right-leq-left-min-ℚ p q q≤p)
      (right-leq-left-max-ℚ p q q≤p)
```

### Maps from rational intervals to rational intervals

```agda
is-interval-map-ℚ :
  (ℚ → ℚ) → ([a,b] [c,d] : interval-ℚ) → UU lzero
is-interval-map-ℚ = is-closed-interval-map-Poset ℚ-Poset ℚ-Poset
```
