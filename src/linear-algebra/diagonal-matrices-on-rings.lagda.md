# Diagonal matrices on rings

```agda
module linear-algebra.diagonal-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.constant-vectors
open import linear-algebra.functoriality-vectors
open import linear-algebra.matrices-on-rings
open import linear-algebra.vectors
open import linear-algebra.vectors-on-rings

open import ring-theory.rings
```

</details>

## Definitions

### Diagonal matrices

```agda
module _
  {l : Level} (R : Ring l)
  where

  diagonal-matrix-Ring : (n : ℕ) → vec-Ring R n → matrix-Ring R n n
  diagonal-matrix-Ring zero-ℕ v = empty-vec
  diagonal-matrix-Ring (succ-ℕ n) (x ∷ v) =
    ( x ∷ zero-vec-Ring R) ∷
    ( map-vec (λ v' → zero-Ring R ∷ v') (diagonal-matrix-Ring n v))
```

### Scalar matrices

```agda
module _
  {l : Level} (R : Ring l)
  where

  scalar-matrix-Ring : (n : ℕ) → type-Ring R → matrix-Ring R n n
  scalar-matrix-Ring n x = diagonal-matrix-Ring R n (constant-vec x)

  identity-matrix-Ring : (n : ℕ) → matrix-Ring R n n
  identity-matrix-Ring n = scalar-matrix-Ring n (one-Ring R)
```
