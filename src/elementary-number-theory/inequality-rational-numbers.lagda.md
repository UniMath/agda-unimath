# Inequality on the rational numbers

```agda
module elementary-number-theory.inequality-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-integer-fractions
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A rational number `x` is less (or equal) to a rational number `y` if and only if
the underlying fraction of `x` is less (or equal) than the underlying fraction
of `y`.

## Definition

### Inequality on the rational numbers

```agda
leq-ℚ-Prop : ℚ → ℚ → Prop lzero
leq-ℚ-Prop (x , px) (y , py) = leq-fraction-ℤ-Prop x y

leq-ℚ : ℚ → ℚ → UU lzero
leq-ℚ x y = type-Prop (leq-ℚ-Prop x y)

is-prop-leq-ℚ : (x y : ℚ) → is-prop (leq-ℚ x y)
is-prop-leq-ℚ x y = is-prop-type-Prop (leq-ℚ-Prop x y)
```

### Strict inequality on the rational numbers

```agda
le-ℚ-Prop : ℚ → ℚ → Prop lzero
le-ℚ-Prop (x , px) (y , py) = le-fraction-ℤ-Prop x y

le-ℚ : ℚ → ℚ → UU lzero
le-ℚ x y = type-Prop (le-ℚ-Prop x y)

is-prop-le-ℚ : (x y : ℚ) → is-prop (le-ℚ x y)
is-prop-le-ℚ x y = is-prop-type-Prop (le-ℚ-Prop x y)
```
