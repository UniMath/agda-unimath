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

### The Ackermann-Péter function

```agda
ackermann-péter-ℕ : ℕ → ℕ → ℕ
ackermann-péter-ℕ zero-ℕ n =
  succ-ℕ n
ackermann-péter-ℕ (succ-ℕ m) zero-ℕ =
  ackermann-péter-ℕ m 1
ackermann-péter-ℕ (succ-ℕ m) (succ-ℕ n) =
  ackermann-péter-ℕ m (ackermann-péter-ℕ (succ-ℕ m) n)
```

### The simplified Ackermann function

```agda
simplified-ackermann-ℕ : ℕ → ℕ
simplified-ackermann-ℕ n = ackermann-péter-ℕ n n
```
