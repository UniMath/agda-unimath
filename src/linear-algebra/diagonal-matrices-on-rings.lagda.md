# Diagonal grids on rings

```agda
module linear-algebra.diagonal-grids-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.constant-tuples
open import linear-algebra.grids-on-rings
open import linear-algebra.tuples-on-rings

open import lists.functoriality-tuples
open import lists.tuples

open import ring-theory.rings
```

</details>

## Definitions

A
{{#concept "diagonal grid" Agda=diagonal-grid-Ring WD="diagonal grid" WDID=Q332791}}
is a [grid](linear-algebra.grids.md) whose only nonzero elements are on the
diagonal of the grid.

### Diagonal grids

```agda
module _
  {l : Level} (R : Ring l)
  where

  diagonal-grid-Ring : (n : ℕ) → tuple-Ring R n → grid-Ring R n n
  diagonal-grid-Ring zero-ℕ v = empty-tuple
  diagonal-grid-Ring (succ-ℕ n) (x ∷ v) =
    ( x ∷ zero-tuple-Ring R) ∷
    ( map-tuple (λ v' → zero-Ring R ∷ v') (diagonal-grid-Ring n v))
```

### Scalar grids

```agda
module _
  {l : Level} (R : Ring l)
  where

  scalar-grid-Ring : (n : ℕ) → type-Ring R → grid-Ring R n n
  scalar-grid-Ring n x = diagonal-grid-Ring R n (constant-tuple x)

  identity-grid-Ring : (n : ℕ) → grid-Ring R n n
  identity-grid-Ring n = scalar-grid-Ring n (one-Ring R)
```
