# Closed interval preserving endomaps on the rational numbers

```agda
module elementary-number-theory.closed-interval-preserving-maps-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.universe-levels

open import order-theory.closed-interval-preserving-maps-posets
```

</details>

## Idea

A map from the [rational numbers](elementary-number-theory.rational-numbers.md)
to themselves `f : ℚ → ℚ` is
{{#concept "closed interval preserving" Agda=is-closed-interval-map-ℚ disambiguation="map between rational numbers"}}
if the [image](foundation.images-subtypes.md) of a
[closed interval](elementary-number-theory.closed-intervals-rational-numbers.md)
is always a closed interval in `Y`. Equivalently, it is a
[closed interval preserving map](order-theory.closed-interval-preserving-maps-total-orders.md)
on the
[total order of rational numbers](elementary-number-theory.decidable-total-order-rational-numbers.md).

## Definition

```agda
is-closed-interval-map-ℚ :
  (ℚ → ℚ) → ([a,b] [c,d] : closed-interval-ℚ) → UU lzero
is-closed-interval-map-ℚ = is-closed-interval-map-Poset ℚ-Poset ℚ-Poset

is-closed-interval-map-prop-ℚ :
  (ℚ → ℚ) → closed-interval-ℚ → closed-interval-ℚ →
  Prop lzero
is-closed-interval-map-prop-ℚ =
  is-closed-interval-map-prop-Poset ℚ-Poset ℚ-Poset
```
