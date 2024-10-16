# The Ackermann function

```agda
module elementary-number-theory.ackermann-function where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
```

</details>

## Idea

The
{{#concept "Ackermann function" WD="Ackermann function" WDID=Q341835 Agda=ackermann}}
is a fast growing binary operation on the natural numbers.

## Definition

```agda
ackermann : ℕ → ℕ → ℕ
ackermann zero-ℕ n = succ-ℕ n
ackermann (succ-ℕ m) zero-ℕ = ackermann m 1
ackermann (succ-ℕ m) (succ-ℕ n) = ackermann m (ackermann (succ-ℕ m) n)
```
