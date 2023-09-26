# Pythagorean triples

```agda
module elementary-number-theory.pythagorean-triples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.squares-natural-numbers

open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A Pythagorean triple is a triple `(a,b,c)` of natural numbers such that
`a² + b² = c²`.

## Definition

```agda
is-pythagorean-triple : ℕ → ℕ → ℕ → UU lzero
is-pythagorean-triple a b c = ((square-ℕ a) +ℕ (square-ℕ b) ＝ square-ℕ c)
```
