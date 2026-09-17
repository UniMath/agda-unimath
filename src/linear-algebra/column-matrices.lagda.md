# Column matrices

```agda
module linear-algebra.column-matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.matrices

open import lists.finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A {{#concept "column matrix" Agda=column-matrix}} of length `n` is a
[matrix](linear-algebra.matrices.md) with `n` rows and one column.

## Definition

```agda
column-matrix : {l : Level} → UU l → ℕ → UU l
column-matrix A n = matrix A n 1

column-matrix-fin-sequence :
  {l : Level} {A : UU l} (n : ℕ) → fin-sequence A n → column-matrix A n
column-matrix-fin-sequence n u = single-fin-sequence ∘ u

fin-sequence-column-matrix :
  {l : Level} {A : UU l} (n : ℕ) → column-matrix A n → fin-sequence A n
fin-sequence-column-matrix n u i = u i (neg-one-Fin 0)
```

## Properties

### The correspondence between finite sequences and column matrices is an equivalence

```agda
module _
  {l : Level}
  {A : UU l}
  (n : ℕ)
  where

  abstract
    is-section-fin-sequence-column-matrix :
      (x : column-matrix A n) →
      column-matrix-fin-sequence n (fin-sequence-column-matrix n x) ＝ x
    is-section-fin-sequence-column-matrix x =
      eq-binary-htpy _ _ ( λ { i (inr star) → refl})

    is-retraction-fin-sequence-column-matrix :
      (x : fin-sequence A n) →
      fin-sequence-column-matrix n (column-matrix-fin-sequence n x) ＝ x
    is-retraction-fin-sequence-column-matrix x = refl

  is-equiv-column-matrix-fin-sequence :
    is-equiv (column-matrix-fin-sequence {l} {A} n)
  is-equiv-column-matrix-fin-sequence =
    is-equiv-is-invertible
      ( fin-sequence-column-matrix n)
      ( is-section-fin-sequence-column-matrix)
      ( is-retraction-fin-sequence-column-matrix)

  equiv-column-matrix-fin-sequence :
    fin-sequence A n ≃ column-matrix A n
  equiv-column-matrix-fin-sequence =
    ( column-matrix-fin-sequence n ,
      is-equiv-column-matrix-fin-sequence)
```
