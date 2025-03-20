# Matrices

```agda
open import foundation.function-extensionality-axiom

module
  linear-algebra.matrices
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.contractible-types funext
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.universe-levels

open import linear-algebra.functoriality-vectors funext
open import linear-algebra.vectors funext
```

</details>

## Idea

An `(m × n)`-matrix of elements in `A` is an arrangement of elements of A with
`m` rows and `n` columns. In other words, a matrix is vector of length `m` of
vectors of length `n` of elements of `A`.

## Definitions

### Matrices

```agda
matrix : {l : Level} (A : UU l) → ℕ → ℕ → UU l
matrix A m n = vec (vec A n) m
```

### The top row of a matrix

```agda
top-row-matrix :
  {l : Level} {m n : ℕ} {A : UU l} → matrix A (succ-ℕ m) n → vec A n
top-row-matrix (v ∷ M) = v
```

### The left column of a matrix

```agda
left-column-matrix :
  {l : Level} {m n : ℕ} {A : UU l} → matrix A m (succ-ℕ n) → vec A m
left-column-matrix = map-vec head-vec
```

### The vertical tail of a matrix

```agda
vertical-tail-matrix :
  {l : Level} {m n : ℕ} {A : UU l} → matrix A (succ-ℕ m) n → matrix A m n
vertical-tail-matrix M = tail-vec M
```

### The horizontal tail of a matrix

```agda
horizontal-tail-matrix :
  {l : Level} {m n : ℕ} {A : UU l} → matrix A m (succ-ℕ n) → matrix A m n
horizontal-tail-matrix = map-vec tail-vec
```

### The vertically empty matrix

```agda
vertically-empty-matrix :
  {l : Level} {n : ℕ} {A : UU l} → matrix A 0 n
vertically-empty-matrix = empty-vec

eq-vertically-empty-matrix :
  {l : Level} {n : ℕ} {A : UU l}
  (x : matrix A 0 n) → Id vertically-empty-matrix x
eq-vertically-empty-matrix empty-vec = refl

is-contr-matrix-zero-ℕ :
  {l : Level} {n : ℕ} {A : UU l} → is-contr (matrix A 0 n)
pr1 is-contr-matrix-zero-ℕ = vertically-empty-matrix
pr2 is-contr-matrix-zero-ℕ = eq-vertically-empty-matrix
```

### The horizontally empty matrix

```agda
horizontally-empty-matrix :
  {l : Level} {m : ℕ} {A : UU l} → matrix A m 0
horizontally-empty-matrix {m = zero-ℕ} = empty-vec
horizontally-empty-matrix {m = succ-ℕ m} = empty-vec ∷ horizontally-empty-matrix

eq-horizontally-empty-matrix :
  {l : Level} {m : ℕ} {A : UU l}
  (x : matrix A m 0) → Id horizontally-empty-matrix x
eq-horizontally-empty-matrix {m = zero-ℕ} empty-vec = refl
eq-horizontally-empty-matrix {m = succ-ℕ m} (empty-vec ∷ M) =
  ap-binary _∷_ refl (eq-horizontally-empty-matrix M)

is-contr-matrix-zero-ℕ' :
  {l : Level} {m : ℕ} {A : UU l} → is-contr (matrix A m 0)
pr1 is-contr-matrix-zero-ℕ' = horizontally-empty-matrix
pr2 is-contr-matrix-zero-ℕ' = eq-horizontally-empty-matrix
```
