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
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A fraction `m/n` is less (or equal) to a fraction `m'/n'` iff `m * n'` is less
(or equal) to `m' * n`.

## Definition

### Inequality of integer fractions

```agda
leq-fraction-ℤ-Prop : fraction-ℤ → fraction-ℤ → Prop lzero
leq-fraction-ℤ-Prop (m , n , p) (m' , n' , p') =
  leq-ℤ-Prop (m *ℤ n') (m' *ℤ n)

leq-fraction-ℤ : fraction-ℤ → fraction-ℤ → UU lzero
leq-fraction-ℤ x y = type-Prop (leq-fraction-ℤ-Prop x y)

is-prop-leq-fraction-ℤ : (x y : fraction-ℤ) → is-prop (leq-fraction-ℤ x y)
is-prop-leq-fraction-ℤ x y = is-prop-type-Prop (leq-fraction-ℤ-Prop x y)
```

### Strict inequality of integer fractions

```agda
le-fraction-ℤ-Prop : fraction-ℤ → fraction-ℤ → Prop lzero
le-fraction-ℤ-Prop (m , n , p) (m' , n' , p') =
  le-ℤ-Prop (m *ℤ n') (m' *ℤ n)

le-fraction-ℤ : fraction-ℤ → fraction-ℤ → UU lzero
le-fraction-ℤ x y = type-Prop (le-fraction-ℤ-Prop x y)

is-prop-le-fraction-ℤ : (x y : fraction-ℤ) → is-prop (le-fraction-ℤ x y)
is-prop-le-fraction-ℤ x y = is-prop-type-Prop (le-fraction-ℤ-Prop x y)
```
