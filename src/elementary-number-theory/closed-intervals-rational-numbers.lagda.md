# Inhabited closed intervals in the rational numbers

```agda
module elementary-number-theory.closed-intervals-rational-numbers where
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

open import order-theory.closed-interval-preserving-maps-posets
open import order-theory.decidable-total-orders
open import order-theory.closed-intervals-posets
```

</details>

## Idea

An
{{#concept "inhabited closed interval" Disambiguation="in the rational numbers" Agda=closed-interval-ℚ}}
in the rational numbers is a
[closed interval](order-theory.closed-intervals-posets.md) in the
[poset](elementary-number-theory.inequality-rational-numbers.md) of
[rational numbers](elementary-number-theory.rational-numbers.md).

## Definition

```agda
closed-interval-ℚ : UU lzero
closed-interval-ℚ = closed-interval-Poset ℚ-Poset

lower-bound-closed-interval-ℚ : closed-interval-ℚ → ℚ
lower-bound-closed-interval-ℚ =
  lower-bound-closed-interval-Poset ℚ-Poset

upper-bound-closed-interval-ℚ : closed-interval-ℚ → ℚ
upper-bound-closed-interval-ℚ =
  upper-bound-closed-interval-Poset ℚ-Poset

subtype-closed-interval-ℚ :
  closed-interval-ℚ → subtype lzero ℚ
subtype-closed-interval-ℚ =
  subtype-closed-interval-Poset ℚ-Poset

is-in-closed-interval-ℚ : closed-interval-ℚ → ℚ → UU lzero
is-in-closed-interval-ℚ [a,b] =
  is-in-subtype (subtype-closed-interval-ℚ [a,b])

is-closed-interval-map-prop-ℚ :
  (ℚ → ℚ) → closed-interval-ℚ → closed-interval-ℚ →
  Prop lzero
is-closed-interval-map-prop-ℚ =
  is-closed-interval-map-prop-Poset ℚ-Poset ℚ-Poset

is-below-prop-closed-interval-ℚ :
  closed-interval-ℚ → subtype lzero ℚ
is-below-prop-closed-interval-ℚ ((a , _) , _) b = le-ℚ-Prop b a

is-above-prop-closed-interval-ℚ :
  closed-interval-ℚ → subtype lzero ℚ
is-above-prop-closed-interval-ℚ ((_ , a) , _) b = le-ℚ-Prop a b

nonnegative-width-closed-interval-ℚ :
  closed-interval-ℚ → ℚ⁰⁺
nonnegative-width-closed-interval-ℚ ((a , b) , a≤b) =
  nonnegative-diff-leq-ℚ a b a≤b

width-closed-interval-ℚ : closed-interval-ℚ → ℚ
width-closed-interval-ℚ [a,b] =
  rational-ℚ⁰⁺ (nonnegative-width-closed-interval-ℚ [a,b])

is-injective-subtype-closed-interval-ℚ :
  is-injective subtype-closed-interval-ℚ
is-injective-subtype-closed-interval-ℚ =
  is-injective-subtype-closed-interval-Poset ℚ-Poset
```

### Important ranges

```agda
zero-zero-closed-interval-ℚ : closed-interval-ℚ
zero-zero-closed-interval-ℚ = ((zero-ℚ , zero-ℚ) , refl-leq-ℚ zero-ℚ)

one-one-closed-interval-ℚ : closed-interval-ℚ
one-one-closed-interval-ℚ = ((one-ℚ , one-ℚ) , refl-leq-ℚ one-ℚ)
```

## Properties

### Characterization of equality

```agda
eq-closed-interval-ℚ :
  ([a,b] [c,d] : closed-interval-ℚ) →
  ( lower-bound-closed-interval-ℚ [a,b] ＝
    lower-bound-closed-interval-ℚ [c,d]) →
  ( upper-bound-closed-interval-ℚ [a,b] ＝
    upper-bound-closed-interval-ℚ [c,d]) →
  [a,b] ＝ [c,d]
eq-closed-interval-ℚ = eq-closed-interval-Poset ℚ-Poset

set-closed-interval-ℚ : Set lzero
set-closed-interval-ℚ = set-closed-interval-Poset ℚ-Poset
```

### Unordered intervals

```agda
unordered-closed-interval-ℚ : ℚ → ℚ → closed-interval-ℚ
unordered-closed-interval-ℚ a b =
  ( (min-ℚ a b , max-ℚ a b) ,
    min-leq-max-Decidable-Total-Order ℚ-Decidable-Total-Order a b)

abstract
  unordered-closed-interval-leq-ℚ :
    (p q : ℚ) → (p≤q : leq-ℚ p q) →
    unordered-closed-interval-ℚ p q ＝ ((p , q) , p≤q)
  unordered-closed-interval-leq-ℚ p q p≤q =
    eq-closed-interval-ℚ _ _
      ( left-leq-right-min-ℚ p q p≤q)
      ( left-leq-right-max-ℚ p q p≤q)

  unordered-closed-interval-leq-ℚ' :
    (p q : ℚ) → (q≤p : leq-ℚ q p) →
    unordered-closed-interval-ℚ p q ＝ ((q , p) , q≤p)
  unordered-closed-interval-leq-ℚ' p q q≤p =
    eq-closed-interval-ℚ _ _
      ( right-leq-left-min-ℚ p q q≤p)
      ( right-leq-left-max-ℚ p q q≤p)
```

### Maps from rational intervals to rational intervals

```agda
is-closed-interval-map-ℚ :
  (ℚ → ℚ) → ([a,b] [c,d] : closed-interval-ℚ) → UU lzero
is-closed-interval-map-ℚ = is-closed-interval-map-Poset ℚ-Poset ℚ-Poset
```
