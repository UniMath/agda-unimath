# Upper bounds of families of MacNeille real numbers

```agda
module real-numbers.upper-bounds-families-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import order-theory.upper-bounds-large-posets

open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.macneille-real-numbers
```

</details>

## Idea

An
{{#concept "upper bound" Disambiguation="on a family of MacNeille real numbers" Agda=is-upper-bound-family-of-elements-macneille-ℝ}}
of a family of [MacNeille real numbers](real-numbers.macneille-real-numbers.md)
`y : I → ℝ` is a MacNeille real number `x` such that for all `i` we have
`yᵢ ≤ x`. In other words, it is an
[upper bound](order-theory.upper-bounds-large-posets.md) in the
[ordering on the MacNeille reals](real-numbers.inequality-macneille-real-numbers.md).

## Definition

```agda
is-upper-bound-family-of-elements-macneille-ℝ :
  {l1 l2 l3 : Level} {I : UU l1} (y : I → macneille-ℝ l2) →
  macneille-ℝ l3 → UU (l1 ⊔ l2 ⊔ l3)
is-upper-bound-family-of-elements-macneille-ℝ y =
  is-upper-bound-family-of-elements-Large-Poset (large-poset-macneille-ℝ) y
```
