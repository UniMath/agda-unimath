# Interior closed intervals in the rational numbers

```agda
module elementary-number-theory.interior-closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

Given two
[closed intervals of rational numbers](elementary-number-theory.closed-intervals-rational-numbers.md)
`[a, b]` and `[c, d]`, then `[c, d]` is said to be
{{#concept "interior" Disambiguation="closed intervals of rational numbers" Agda=is-interior-closed-interval-ℚ}}
to `[a, b]` if `a < c` and `d < b`.

## Definition

```agda
is-interior-prop-closed-interval-ℚ :
  closed-interval-ℚ → closed-interval-ℚ → Prop lzero
is-interior-prop-closed-interval-ℚ ((x , y) , _) ((x' , y') , _) =
  le-ℚ-Prop x x' ∧ le-ℚ-Prop y' y

is-interior-closed-interval-ℚ : closed-interval-ℚ → closed-interval-ℚ → UU lzero
is-interior-closed-interval-ℚ [x,y] [x',y'] =
  type-Prop (is-interior-prop-closed-interval-ℚ [x,y] [x',y'])
```
