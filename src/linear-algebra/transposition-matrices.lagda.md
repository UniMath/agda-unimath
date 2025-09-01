# Transposition of matrices

```agda
module linear-algebra.transposition-matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.matrices

open import lists.functoriality-tuples
open import lists.tuples
```

</details>

## Idea

The
{{#concept "transposition of a matrix" WD="matrix transposition" WDID=Q77961711 Agda=transpose-matrix}}
is the operation on [matrices](linear-algebra.matrices.md) that turns rows into
columns and columns into rows.

## Definition

```agda
transpose-matrix :
  {l : Level} → {A : UU l} → {m n : ℕ} → matrix A m n → matrix A n m
transpose-matrix {n = zero-ℕ} x = empty-tuple
transpose-matrix {n = succ-ℕ n} x =
  map-tuple head-tuple x ∷ transpose-matrix (map-tuple tail-tuple x)
```

## Properties

```agda
is-involution-transpose-matrix :
  {l : Level} → {A : UU l} → {m n : ℕ} →
  (x : matrix A m n) → Id x (transpose-matrix (transpose-matrix x))
is-involution-transpose-matrix {m = zero-ℕ} empty-tuple = refl
is-involution-transpose-matrix {m = succ-ℕ m} (r ∷ rs) =
  ( ap (_∷_ r) (is-involution-transpose-matrix rs)) ∙
  ( ap-binary _∷_
    ( lemma-first-row r rs) (ap transpose-matrix (lemma-rest r rs)))
  where
  lemma-first-row :
    {l : Level} → {A : UU l} → {m n : ℕ} → (x : tuple A n) →
    (xs : matrix A m n) →
    Id x (map-tuple head-tuple (transpose-matrix (x ∷ xs)))
  lemma-first-row {n = zero-ℕ} empty-tuple _ = refl
  lemma-first-row {n = succ-ℕ m} (k ∷ ks) xs =
    ap (_∷_ k) (lemma-first-row ks (map-tuple tail-tuple xs))

  lemma-rest :
    {l : Level} → {A : UU l} → {m n : ℕ} → (x : tuple A n) →
    (xs : matrix A m n) →
    transpose-matrix xs ＝ map-tuple tail-tuple (transpose-matrix (x ∷ xs))
  lemma-rest {n = zero-ℕ} empty-tuple xs = refl
  lemma-rest {n = succ-ℕ n} (k ∷ ks) xs =
    ap
      ( _∷_ (map-tuple head-tuple xs))
      ( lemma-rest (tail-tuple (k ∷ ks)) (map-tuple tail-tuple xs))
```
