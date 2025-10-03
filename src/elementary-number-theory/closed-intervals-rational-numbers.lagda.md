# Closed intervals in the rational numbers

```agda
module elementary-number-theory.closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.closed-interval-preserving-maps-posets
open import order-theory.closed-intervals-posets
open import order-theory.decidable-total-orders
```

</details>

## Idea

An
{{#concept "closed interval" Disambiguation="in the rational numbers" Agda=closed-interval-ℚ}}
in the rational numbers is a
[closed interval](order-theory.closed-intervals-posets.md) in the
[poset](elementary-number-theory.inequality-rational-numbers.md) of
[rational numbers](elementary-number-theory.rational-numbers.md). Note, in
particular, that we thus consider closed intervals to be inhabited by
convention.

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

is-below-prop-closed-interval-ℚ : closed-interval-ℚ → subtype lzero ℚ
is-below-prop-closed-interval-ℚ ((a , _) , _) b = le-ℚ-Prop b a

is-below-closed-interval-ℚ : closed-interval-ℚ → ℚ → UU lzero
is-below-closed-interval-ℚ [a,b] q =
  type-Prop (is-below-prop-closed-interval-ℚ [a,b] q)

is-above-prop-closed-interval-ℚ :
  closed-interval-ℚ → subtype lzero ℚ
is-above-prop-closed-interval-ℚ ((_ , a) , _) b = le-ℚ-Prop a b

is-above-closed-interval-ℚ : closed-interval-ℚ → ℚ → UU lzero
is-above-closed-interval-ℚ [a,b] q =
  type-Prop (is-above-prop-closed-interval-ℚ [a,b] q)

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

is-nontrivial-prop-closed-interval-ℚ : closed-interval-ℚ → Prop lzero
is-nontrivial-prop-closed-interval-ℚ ((a , b) , _) = le-ℚ-Prop a b

is-nontrivial-closed-interval-ℚ : closed-interval-ℚ → UU lzero
is-nontrivial-closed-interval-ℚ [a,b] =
  type-Prop (is-nontrivial-prop-closed-interval-ℚ [a,b])
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

### Interior intervals

```agda
is-interior-prop-closed-interval-ℚ :
  closed-interval-ℚ → closed-interval-ℚ → Prop lzero
is-interior-prop-closed-interval-ℚ ((x , y) , _) ((x' , y') , _) =
  le-ℚ-Prop x x' ∧ le-ℚ-Prop y' y

is-interior-closed-interval-ℚ : closed-interval-ℚ → closed-interval-ℚ → UU lzero
is-interior-closed-interval-ℚ [x,y] [x',y'] =
  type-Prop (is-interior-prop-closed-interval-ℚ [x,y] [x',y'])
```

### The bounds of a closed interval are elements

```agda
lower-bound-is-in-closed-interval-ℚ :
  ([a,b] : closed-interval-ℚ) →
  is-in-closed-interval-ℚ [a,b] (lower-bound-closed-interval-ℚ [a,b])
lower-bound-is-in-closed-interval-ℚ =
  lower-bound-is-in-closed-interval-Poset ℚ-Poset

upper-bound-is-in-closed-interval-ℚ :
  ([a,b] : closed-interval-ℚ) →
  is-in-closed-interval-ℚ [a,b] (upper-bound-closed-interval-ℚ [a,b])
upper-bound-is-in-closed-interval-ℚ =
  upper-bound-is-in-closed-interval-Poset ℚ-Poset
```

### The distance between the lower and upper bounds of a closed interval is its width

```agda
abstract
  eq-width-dist-lower-upper-bounds-closed-interval-ℚ :
    ([a,b] : closed-interval-ℚ) →
    rational-dist-ℚ
      ( lower-bound-closed-interval-ℚ [a,b])
      ( upper-bound-closed-interval-ℚ [a,b]) ＝
    width-closed-interval-ℚ [a,b]
  eq-width-dist-lower-upper-bounds-closed-interval-ℚ ((a , b) , a≤b) =
    eq-dist-diff-leq-ℚ a b a≤b

  eq-width-dist-upper-lower-bounds-closed-interval-ℚ :
    ([a,b] : closed-interval-ℚ) →
    rational-dist-ℚ
      ( upper-bound-closed-interval-ℚ [a,b])
      ( lower-bound-closed-interval-ℚ [a,b]) ＝
    width-closed-interval-ℚ [a,b]
  eq-width-dist-upper-lower-bounds-closed-interval-ℚ ((a , b) , a≤b) =
    eq-dist-diff-leq-ℚ' b a a≤b
```
