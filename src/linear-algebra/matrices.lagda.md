# Matrices

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.matrices where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.contractible-types using (is-contr)
open import foundation.identity-types using (Id; refl; ap-binary)
open import foundation.universe-levels using (UU; Level)

open import linear-algebra.functoriality-vectors using (map-vec)
open import linear-algebra.vectors using (vec; _∷_; empty-vec; head; tail)
```

## Idea

An `(m × n)`-matrix of elements in `A` is an arrangement of elements of A with `m` rows and `n` columns. In other words, a matrix is vector of length `m` of vectors of length `n` of elements of `A`.

##  Definitions

### Matrices

```agda
Mat : {l : Level} (A : UU l) → ℕ → ℕ → UU l
Mat A m n = vec (vec A n) m
```

### The top row of a matrix

```agda
top-row-Mat : {l : Level} {m n : ℕ} {A : UU l} → Mat A (succ-ℕ m) n → vec A n
top-row-Mat (v ∷ M) = v
```

### The left column of a matrix

```agda
left-column-Mat :
  {l : Level} {m n : ℕ} {A : UU l} → Mat A m (succ-ℕ n) → vec A m
left-column-Mat = map-vec head
```

### The vertical tail of a matrix

```agda
vertical-tail-Mat :
  {l : Level} {m n : ℕ} {A : UU l} → Mat A (succ-ℕ m) n → Mat A m n
vertical-tail-Mat M = tail M
```

### The horizontal tail of a matrix

```agda
horizontal-tail-Mat :
  {l : Level} {m n : ℕ} {A : UU l} → Mat A m (succ-ℕ n) → Mat A m n
horizontal-tail-Mat = map-vec tail
```

### The vertically empty matrix

```agda
vertically-empty-Mat :
  {l : Level} {n : ℕ} {A : UU l} → Mat A 0 n
vertically-empty-Mat = empty-vec

eq-vertically-empty-Mat :
  {l : Level} {n : ℕ} {A : UU l} (x : Mat A 0 n) → Id vertically-empty-Mat x
eq-vertically-empty-Mat empty-vec = refl

is-contr-Mat-zero-ℕ :
  {l : Level} {n : ℕ} {A : UU l} → is-contr (Mat A 0 n)
pr1 is-contr-Mat-zero-ℕ = vertically-empty-Mat
pr2 is-contr-Mat-zero-ℕ = eq-vertically-empty-Mat
```

### The horizontally empty matrix

```agda
horizontally-empty-Mat :
  {l : Level} {m : ℕ} {A : UU l} → Mat A m 0
horizontally-empty-Mat {m = zero-ℕ} = empty-vec
horizontally-empty-Mat {m = succ-ℕ m} = empty-vec ∷ horizontally-empty-Mat

eq-horizontally-empty-Mat :
  {l : Level} {m : ℕ} {A : UU l} (x : Mat A m 0) → Id horizontally-empty-Mat x
eq-horizontally-empty-Mat {m = zero-ℕ} empty-vec = refl
eq-horizontally-empty-Mat {m = succ-ℕ m} (empty-vec ∷ M) =
  ap-binary _∷_ refl (eq-horizontally-empty-Mat M)

is-contr-Mat-zero-ℕ' :
  {l : Level} {m : ℕ} {A : UU l} → is-contr (Mat A m 0)
pr1 is-contr-Mat-zero-ℕ' = horizontally-empty-Mat
pr2 is-contr-Mat-zero-ℕ' = eq-horizontally-empty-Mat
```
