# Vectors

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.vectors where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.identity-types using
  ( Id; refl; ap; ap-binary; _∙_; inv)
open import foundation.universe-levels using (UU ; Level ; lzero)
```
## Idea

An vector of elements of type `A` of length `n` is a list of `n` elements of type `A`.

## Definition

```agda
infixr 5 _∷_

data vec {l : Level} (A : UU l) : ℕ → UU l where
  empty-vec : vec A zero-ℕ
  _∷_ : ∀ {n} → A → vec A n → vec A (succ-ℕ n)

head : {l : Level} {A : UU l} {n : ℕ} → vec A (succ-ℕ n) → A
head (x ∷ v) = x

tail : {l : Level} {A : UU l} {n : ℕ} → vec A (succ-ℕ n) → vec A n
tail (x ∷ v) = v
```
