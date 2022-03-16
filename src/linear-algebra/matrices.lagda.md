# Matrices

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.matrices where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.universe-levels using (UU; Level)

open import linear-algebra.vectors using (vec)
```

## Idea

An `(m × n)`-matrix of elements in `A` is a vector of length `m` of vectors of length `n` of elements of `A`.

##  Definition

The definition is based on exercises from [Computer Aided Formal Reasoning](http://www.cs.nott.ac.uk/~psztxa/g53cfr/)

Alternatively, an m × n could be seen as map-vec from `(Fin m × Fin n)` to `K`

```agda
Mat : {l : Level} → (K : UU l) → ℕ → ℕ → UU l
Mat K m n = vec (vec K n) m
```
