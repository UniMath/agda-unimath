# The irrationality of the square root of two

```agda
module elementary-number-theory.irrationality-square-root-of-two where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import foundation.dependent-pair-types
open import elementary-number-theory.squares-rational-numbers
open import foundation.negated-equality
```

</details>

## Idea

There is no [rational number](elementary-number-theory.rational-numbers.md)
whose [square](elementary-number-theory.squares-rational-numbers.md) is two.

## Proof

```agda
abstract
  not-two-square-ℚ : (q : ℚ) → square-ℚ q ≠ rational-ℕ 2
  not-two-square-ℚ ((p , q⁺@(q , is-pos-q)) , coprime-p-q) p/q²=2 =
    {!   !}
```
