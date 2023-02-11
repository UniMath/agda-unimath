---
title: The triangular numbers
---

```agda
module elementary-number-theory.triangular-numbers where

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
```

## Definition

```agda
triangular-number-ℕ : ℕ → ℕ
triangular-number-ℕ 0 = 0
triangular-number-ℕ (succ-ℕ n) = add-ℕ (triangular-number-ℕ n) (succ-ℕ n)
```
