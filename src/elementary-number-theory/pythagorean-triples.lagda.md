# Pythagorean triples

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory.pythagorean-triples
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.squares-natural-numbers funext

open import foundation.identity-types funext
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
