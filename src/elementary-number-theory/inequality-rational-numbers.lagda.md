# Inequality on the rational numbers

```agda
module elementary-number-theory.inequality-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-integer-fractions
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A rational `x` is less (or equal) to a rational `y` iff the underlying fraction
of `x` is less (or equal) than the underlying fraction of `y`.

## Definition

```agda
leq-ℚ : ℚ → ℚ → UU lzero
leq-ℚ (x , px) (y , py) = leq-fraction-ℤ x y

le-ℚ : ℚ → ℚ → UU lzero
le-ℚ (x , px) (y , py) = le-fraction-ℤ x y
```
