# Vectors on magmas

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.vectors-on-magmas where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.universe-levels using (Level; UU)

open import linear-algebra.functoriality-vectors using (map-binary-vec)
open import linear-algebra.vectors using (vec)

open import wild-algebra.magmas using (Magma; type-Magma; mul-Magma)
```

## Idea

Given a magma `M`, the type `vec n M` is again a magma.

## Definition

```agda
type-vec-Magma : {l : Level} → Magma l → ℕ → UU l
type-vec-Magma M n = vec (type-Magma M) n

mul-vec-Magma :
  {l : Level} (M : Magma l) {n : ℕ}
  (x y : vec (type-Magma M) n) → vec (type-Magma M) n
mul-vec-Magma M = map-binary-vec (mul-Magma M)

vec-Magma : {l : Level} → Magma l → ℕ → Magma l
pr1 (vec-Magma M n) = type-vec-Magma M n
pr2 (vec-Magma M n) = mul-vec-Magma M
```
