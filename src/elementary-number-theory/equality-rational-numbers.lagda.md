# Equality of rational numbers

```agda
module elementary-number-theory.equality-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.rational-numbers

open import foundation.identity-types
open import foundation.universe-levels

```

</details>

## Idea

An equality predicate is defined by similarity on the underlying integer
fractions. Then we show that this predicate characterizes the identity type of
the rational numbers.

## Definition

```agda
Eq-ℚ : ℚ → ℚ → UU lzero
Eq-ℚ x y = sim-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)

refl-Eq-ℚ : (x : ℚ) → Eq-ℚ x x
refl-Eq-ℚ q = refl-sim-fraction-ℤ (fraction-ℚ q)

Eq-eq-ℚ : {x y : ℚ} → x ＝ y → Eq-ℚ x y
Eq-eq-ℚ {x} {.x} refl = refl-Eq-ℚ x

eq-Eq-ℚ : (x y : ℚ) → Eq-ℚ x y → x ＝ y
eq-Eq-ℚ x y H = equational-reasoning
  x ＝ rational-fraction-ℤ (fraction-ℚ x) by inv (is-retraction-rational-fraction-ℚ x)
  ＝ rational-fraction-ℤ (fraction-ℚ y)  by eq-ℚ-sim-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y) H
  ＝ y by is-retraction-rational-fraction-ℚ y


```
