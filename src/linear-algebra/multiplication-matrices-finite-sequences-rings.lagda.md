# Multiplying matrices and finite sequences

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.multiplication-matrices-finite-sequences-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.column-matrices
open import linear-algebra.column-matrices-on-rings
open import linear-algebra.finite-sequences-in-rings
open import linear-algebra.function-left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings
open import linear-algebra.matrices-on-rings
open import linear-algebra.multiplication-matrices-on-rings

open import ring-theory.rings
open import ring-theory.sums-of-finite-sequences-of-elements-rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The product of an `m × n` [matrix](linear-algebra.matrices-on-rings.md) on a
[ring](ring-theory.rings.md) `R` and a
[finite sequence](linear-algebra.finite-sequences-in-rings.md) `v` of length `n`
in `R` is the `m`-element finite sequence `w` defined as `wᵢ ≔ ∑ⱼ Mᵢⱼ vⱼ`.

## Definition

```agda
module _
  {l : Level}
  (R : Ring l)
  (m n : ℕ)
  where

  mul-matrix-fin-sequence-type-Ring :
    matrix-Ring R m n → fin-sequence-type-Ring R n → fin-sequence-type-Ring R m
  mul-matrix-fin-sequence-type-Ring M v =
    fin-sequence-column-matrix
      ( m)
      ( mul-matrix-Ring R m n 1 M (column-matrix-fin-sequence n v))
```

## See also

- [Multiplication of matrices and finite sequences on commutative rings](linear-algebra.multiplication-matrices-finite-sequences-commutative-rings.md),
  which has many more useful properties (e.g. linearity)
