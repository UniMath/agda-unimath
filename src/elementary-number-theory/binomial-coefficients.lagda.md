# The binomial coefficients

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.binomial-coefficients where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ)
```

## Definition

```agda
_choose-ℕ_ : ℕ → ℕ → ℕ
0 choose-ℕ 0 = 1
0 choose-ℕ succ-ℕ k = 0
(succ-ℕ n) choose-ℕ 0 = 1
(succ-ℕ n) choose-ℕ (succ-ℕ k) = add-ℕ (n choose-ℕ k) (n choose-ℕ (succ-ℕ k))
```
