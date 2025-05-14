# Matrices

```agda
module linear-algebra.matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import lists.functoriality-tuples
open import lists.tuples
```

</details>

## Idea

An `m × n` {{#concept "matrix" Agda=matrix WD="matrix" WDID=Q44337}} of elements
in `A` is an arrangement of elements of A with `m` rows and `n` columns. In
other words, a matrix is a [tuple](lists.tuples.md) of length `m` of tuples of
length `n` of elements of `A`.

## Definitions

### Matrices

```agda
matrix : {l : Level} (A : UU l) → ℕ → ℕ → UU l
matrix A m n = tuple (tuple A n) m
```

### The top row of a matrix

```agda
top-row-matrix :
  {l : Level} {m n : ℕ} {A : UU l} → matrix A (succ-ℕ m) n → tuple A n
top-row-matrix (v ∷ M) = v
```

### The left column of a matrix

```agda
left-column-matrix :
  {l : Level} {m n : ℕ} {A : UU l} → matrix A m (succ-ℕ n) → tuple A m
left-column-matrix = map-tuple head-tuple
```

### The vertical tail of a matrix

```agda
vertical-tail-matrix :
  {l : Level} {m n : ℕ} {A : UU l} → matrix A (succ-ℕ m) n → matrix A m n
vertical-tail-matrix M = tail-tuple M
```

### The horizontal tail of a matrix

```agda
horizontal-tail-matrix :
  {l : Level} {m n : ℕ} {A : UU l} → matrix A m (succ-ℕ n) → matrix A m n
horizontal-tail-matrix = map-tuple tail-tuple
```

### The vertically empty matrix

```agda
vertically-empty-matrix :
  {l : Level} {n : ℕ} {A : UU l} → matrix A 0 n
vertically-empty-matrix = empty-tuple

eq-vertically-empty-matrix :
  {l : Level} {n : ℕ} {A : UU l}
  (x : matrix A 0 n) → Id vertically-empty-matrix x
eq-vertically-empty-matrix empty-tuple = refl

is-contr-matrix-zero-ℕ :
  {l : Level} {n : ℕ} {A : UU l} → is-contr (matrix A 0 n)
pr1 is-contr-matrix-zero-ℕ = vertically-empty-matrix
pr2 is-contr-matrix-zero-ℕ = eq-vertically-empty-matrix
```

### The horizontally empty matrix

```agda
horizontally-empty-matrix :
  {l : Level} {m : ℕ} {A : UU l} → matrix A m 0
horizontally-empty-matrix {m = zero-ℕ} = empty-tuple
horizontally-empty-matrix {m = succ-ℕ m} =
  empty-tuple ∷ horizontally-empty-matrix

eq-horizontally-empty-matrix :
  {l : Level} {m : ℕ} {A : UU l}
  (x : matrix A m 0) → Id horizontally-empty-matrix x
eq-horizontally-empty-matrix {m = zero-ℕ} empty-tuple = refl
eq-horizontally-empty-matrix {m = succ-ℕ m} (empty-tuple ∷ M) =
  ap-binary _∷_ refl (eq-horizontally-empty-matrix M)

is-contr-matrix-zero-ℕ' :
  {l : Level} {m : ℕ} {A : UU l} → is-contr (matrix A m 0)
pr1 is-contr-matrix-zero-ℕ' = horizontally-empty-matrix
pr2 is-contr-matrix-zero-ℕ' = eq-horizontally-empty-matrix
```
