# Transposition of matrices

```agda
open import foundation.function-extensionality-axiom

module
  linear-algebra.transposition-matrices
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.identity-types funext
open import foundation.universe-levels

open import linear-algebra.functoriality-vectors funext
open import linear-algebra.matrices funext
open import linear-algebra.vectors funext
```

</details>

## Idea

The transposition of a matrix is the operation that turns rows into columns and
columns into rows.

## Definition

```agda
transpose-matrix :
  {l : Level} → {A : UU l} → {m n : ℕ} → matrix A m n → matrix A n m
transpose-matrix {n = zero-ℕ} x = empty-vec
transpose-matrix {n = succ-ℕ n} x =
  map-vec head-vec x ∷ transpose-matrix (map-vec tail-vec x)
```

## Properties

```agda
is-involution-transpose-matrix :
  {l : Level} → {A : UU l} → {m n : ℕ} →
  (x : matrix A m n) → Id x (transpose-matrix (transpose-matrix x))
is-involution-transpose-matrix {m = zero-ℕ} empty-vec = refl
is-involution-transpose-matrix {m = succ-ℕ m} (r ∷ rs) =
  ( ap (_∷_ r) (is-involution-transpose-matrix rs)) ∙
  ( ap-binary _∷_
    ( lemma-first-row r rs) (ap transpose-matrix (lemma-rest r rs)))
  where
  lemma-first-row :
    {l : Level} → {A : UU l} → {m n : ℕ} → (x : vec A n) → (xs : matrix A m n) →
    Id x (map-vec head-vec (transpose-matrix (x ∷ xs)))
  lemma-first-row {n = zero-ℕ} empty-vec _ = refl
  lemma-first-row {n = succ-ℕ m} (k ∷ ks) xs =
    ap (_∷_ k) (lemma-first-row ks (map-vec tail-vec xs))

  lemma-rest :
    {l : Level} → {A : UU l} → {m n : ℕ} → (x : vec A n) → (xs : matrix A m n) →
    Id (transpose-matrix xs) (map-vec tail-vec (transpose-matrix (x ∷ xs)))
  lemma-rest {n = zero-ℕ} empty-vec xs = refl
  lemma-rest {n = succ-ℕ n} (k ∷ ks) xs =
    ap
      ( _∷_ (map-vec head-vec xs))
      ( lemma-rest (tail-vec (k ∷ ks)) (map-vec tail-vec xs))
```
