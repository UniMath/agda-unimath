# Increasing endomaps on MacNeille real numbers

```agda
module real-numbers.increasing-endomaps-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets

open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.macneille-real-numbers
```

</details>

## Idea

An endomap on the
[MacNeille real numbers](real-numbers.macneille-real-numbers.md) is
{{#concept "increasing" Disambiguation="endomap on MacNeille reals" Agda=is-increasing-endomap-macneille-ℝ}}
if it preserves the standard order.

## Definition

```agda
is-increasing-prop-endomap-macneille-ℝ :
  {l1 l2 : Level} →
  (macneille-ℝ l1 → macneille-ℝ l2) →
  Prop (lsuc l1 ⊔ l2)
is-increasing-prop-endomap-macneille-ℝ {l1} {l2} =
  preserves-order-prop-Poset
    ( poset-macneille-ℝ l1)
    ( poset-macneille-ℝ l2)

is-increasing-endomap-macneille-ℝ :
  {l1 l2 : Level} →
  (macneille-ℝ l1 → macneille-ℝ l2) →
  UU (lsuc l1 ⊔ l2)
is-increasing-endomap-macneille-ℝ f =
  type-Prop (is-increasing-prop-endomap-macneille-ℝ f)
```
