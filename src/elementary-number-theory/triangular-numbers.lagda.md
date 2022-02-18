# The triangular numbers

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.triangular-numbers where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ)
```

## Definition

```agda
triangular-number-ℕ : ℕ → ℕ
triangular-number-ℕ 0 = 0
triangular-number-ℕ (succ-ℕ n) = add-ℕ (triangular-number-ℕ n) (succ-ℕ n)
```
