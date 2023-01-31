# Diagonal matrices on rings

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.diagonal-matrices-on-rings where

open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.constant-vectors using (constant-vec)
open import linear-algebra.functoriality-vectors using (map-vec)
open import linear-algebra.matrices-on-rings using (matrix-Ring)
open import linear-algebra.vectors using (empty-vec; _∷_; vec)
open import linear-algebra.vectors-on-rings using (vec-Ring; zero-vec-Ring)

open import ring-theory.rings using
  ( Ring; type-Ring; zero-Ring; one-Ring)
```

## Definitions

### Diagonal matrices

```agda
module _
  {l : Level} (R : Ring l)
  where

  diagonal-matrix-Ring : (n : ℕ) → vec-Ring R n → matrix-Ring R n n
  diagonal-matrix-Ring zero-ℕ v = empty-vec
  diagonal-matrix-Ring (succ-ℕ n) (x ∷ v) =
    (x ∷ zero-vec-Ring R) ∷ map-vec (λ v' → zero-Ring R ∷ v') (diagonal-matrix-Ring n v)
```

### Scalar matrices

```
module _
  {l : Level} (R : Ring l)
  where

  scalar-matrix-Ring : (n : ℕ) → type-Ring R → matrix-Ring R n n
  scalar-matrix-Ring n x = diagonal-matrix-Ring R n (constant-vec x)

  identity-matrix-Ring : (n : ℕ) → matrix-Ring R n n
  identity-matrix-Ring n = scalar-matrix-Ring n (one-Ring R)
```
