# Inequality on integer fractions

```agda
module elementary-number-theory.inequality-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.multiplication-integers

open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A fraction `m/n` is less (or equal) to a fraction `m'/n'` iff `m * n'` is less
(or equal) to `m' * n`.

## Definition

```agda
leq-fraction-ℤ : fraction-ℤ → fraction-ℤ → UU lzero
leq-fraction-ℤ (m , n , p) (m' , n' , p') =
  leq-ℤ (mul-ℤ m n') (mul-ℤ m' n)

le-fraction-ℤ : fraction-ℤ → fraction-ℤ → UU lzero
le-fraction-ℤ (m , n , p) (m' , n' , p') =
  le-ℤ (mul-ℤ m n') (mul-ℤ m' n)
```
