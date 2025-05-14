# Diagonal matrices on rings

```agda
module linear-algebra.diagonal-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.constant-tuples
open import linear-algebra.matrices-on-rings
open import linear-algebra.tuples-on-rings

open import lists.functoriality-tuples
open import lists.tuples

open import ring-theory.rings
```

</details>

## Definitions

A
{{#concept "diagonal matrix" Agda=diagonal-matrix-Ring WD="diagonal matrix" WDID=Q332791}}
is a [matrix](linear-algebra.matrices.md) whose only nonzero elements are on the
diagonal of the matrix.

### Diagonal matrices

```agda
module _
  {l : Level} (R : Ring l)
  where

  diagonal-matrix-Ring : (n : ℕ) → tuple-Ring R n → matrix-Ring R n n
  diagonal-matrix-Ring zero-ℕ v = empty-tuple
  diagonal-matrix-Ring (succ-ℕ n) (x ∷ v) =
    ( x ∷ zero-tuple-Ring R) ∷
    ( map-tuple (λ v' → zero-Ring R ∷ v') (diagonal-matrix-Ring n v))
```

### Scalar matrices

```agda
module _
  {l : Level} (R : Ring l)
  where

  scalar-matrix-Ring : (n : ℕ) → type-Ring R → matrix-Ring R n n
  scalar-matrix-Ring n x = diagonal-matrix-Ring R n (constant-tuple x)

  identity-matrix-Ring : (n : ℕ) → matrix-Ring R n n
  identity-matrix-Ring n = scalar-matrix-Ring n (one-Ring R)
```
