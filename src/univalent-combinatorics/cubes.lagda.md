# Cubes

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.cubes where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.universe-levels using (UU; lsuc; lzero)

open import univalent-combinatorics.complements-isolated-points using
  ( complement-point-UU-Fin; inclusion-complement-point-UU-Fin)
open import univalent-combinatorics.finite-types using
  ( UU-Fin; type-UU-Fin; has-cardinality; has-finite-cardinality; is-finite;
    is-finite-has-finite-cardinality; is-finite-has-cardinality; Fin-UU-Fin)
```

## Definitions

### Cubes

```agda
cube : ℕ → UU (lsuc lzero)
cube k = Σ (UU-Fin k) (λ X → type-UU-Fin X → UU-Fin 2)

dim-cube-UU-Fin : {k : ℕ} (X : cube k) → UU-Fin k
dim-cube-UU-Fin X = pr1 X

dim-cube : {k : ℕ} → cube k → UU lzero
dim-cube X = type-UU-Fin (dim-cube-UU-Fin X)

has-cardinality-dim-cube :
  {k : ℕ} (X : cube k) → has-cardinality k (dim-cube X)
has-cardinality-dim-cube X =
  pr2 (dim-cube-UU-Fin X)

has-finite-cardinality-dim-cube :
  {k : ℕ} (X : cube k) → has-finite-cardinality (dim-cube X)
has-finite-cardinality-dim-cube {k} X =
  pair k (pr2 (dim-cube-UU-Fin X))

is-finite-dim-cube :
  {k : ℕ} (X : cube k) → is-finite (dim-cube X)
is-finite-dim-cube X =
  is-finite-has-finite-cardinality (has-finite-cardinality-dim-cube X)

axis-cube-UU-2 :
  {k : ℕ} (X : cube k) → dim-cube X → UU-Fin 2
axis-cube-UU-2 X = pr2 X

axis-cube : {k : ℕ} (X : cube k) → dim-cube X → UU lzero
axis-cube X d = type-UU-Fin (axis-cube-UU-2 X d)

has-cardinality-axis-cube :
  {k : ℕ} (X : cube k) (d : dim-cube X) → has-cardinality 2 (axis-cube X d)
has-cardinality-axis-cube X d = pr2 (axis-cube-UU-2 X d)

has-finite-cardinality-axis-cube :
  {k : ℕ} (X : cube k) (d : dim-cube X) → has-finite-cardinality (axis-cube X d)
has-finite-cardinality-axis-cube X d =
  pair 2 (has-cardinality-axis-cube X d)

is-finite-axis-cube :
  {k : ℕ} (X : cube k) (d : dim-cube X) → is-finite (axis-cube X d)
is-finite-axis-cube X d =
  is-finite-has-cardinality (has-cardinality-axis-cube X d)
```

### Vertices of cubes

```agda
vertex-cube : {k : ℕ} (X : cube k) → UU lzero
vertex-cube X = (d : dim-cube X) → axis-cube X d
```

### The standard cube

```agda
dim-standard-cube-UU-Fin : (k : ℕ) → UU-Fin k
dim-standard-cube-UU-Fin k = Fin-UU-Fin k

dim-standard-cube : ℕ → UU lzero
dim-standard-cube k = type-UU-Fin (dim-standard-cube-UU-Fin k)

axis-standard-cube-UU-Fin : (k : ℕ) → dim-standard-cube k → UU-Fin 2
axis-standard-cube-UU-Fin k d = Fin-UU-Fin 2

axis-standard-cube : (k : ℕ) → dim-standard-cube k → UU lzero
axis-standard-cube k d = type-UU-Fin (axis-standard-cube-UU-Fin k d)

standard-cube : (k : ℕ) → cube k
standard-cube k =
  pair (dim-standard-cube-UU-Fin k) (axis-standard-cube-UU-Fin k)

{-
mere-equiv-standard-cube :
  {k : ℕ} (X : cube k) → type-trunc-Prop (equiv-cube (standard-cube k) X)
mere-equiv-standard-cube {k} (pair (pair X H) Y) =
  apply-universal-property-trunc-Prop H
    ( trunc-Prop (equiv-cube (standard-cube k) (pair (pair X H) Y)))
    ( λ e →
      {! finite-choice-count (pair k e) ?!})
-}
```

### Faces of cubes

```agda
face-cube :
  {k : ℕ} (X : cube (succ-ℕ k)) (d : dim-cube X) (a : axis-cube X d) → cube k
face-cube X d a =
  pair ( complement-point-UU-Fin (pair (dim-cube-UU-Fin X) d))
       ( λ d' →
         axis-cube-UU-2 X
           ( inclusion-complement-point-UU-Fin
             ( pair (dim-cube-UU-Fin X) d) d'))
```
