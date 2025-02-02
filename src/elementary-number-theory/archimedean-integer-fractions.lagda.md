# The Archimedean property of integer fractions

```agda
module elementary-number-theory.archimedean-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.archimedean-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-integer-fractions
open import elementary-number-theory.strict-inequality-integer-fractions
open import elementary-number-theory.strict-inequality-integers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Definition

The Archimedean property of the integer fractions is that for any positive
integer fraction `x` and integer fraction `y`, there is an `n : ℕ` such that
`y < in-fraction-ℤ (int-ℕ n) *fraction-ℤ x`.

```agda
archimedean-property-fraction-ℤ :
  (x y : fraction-ℤ) →
    is-positive-fraction-ℤ x →
    Σ ℕ λ n → le-fraction-ℤ y (in-fraction-ℤ (int-ℕ n) *fraction-ℤ x)
archimedean-property-fraction-ℤ (px , qx , pos-qx) (py , qy , pos-qy) pos-px =
  ind-Σ
    (λ n H → n ,
      tr
        (le-ℤ (py *ℤ qx))
        (inv (associative-mul-ℤ (int-ℕ n) px qy))
        H)
    (archimedean-property-ℤ
      (px *ℤ qy)
      (py *ℤ qx)
      (is-positive-mul-ℤ pos-px pos-qy))
```
