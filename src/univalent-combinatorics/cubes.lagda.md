# Cubes

```agda
module univalent-combinatorics.cubes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.complements-isolated-points
open import univalent-combinatorics.finite-types
```

</details>

## Definitions

### Cubes

```agda
cube : ℕ → UU (lsuc lzero)
cube k = Σ (UU-Fin lzero k) (λ X → type-UU-Fin k X → UU-Fin lzero 2)

module _
  (k : ℕ) (X : cube k)
  where

  dim-cube-UU-Fin : UU-Fin lzero k
  dim-cube-UU-Fin = pr1 X

  dim-cube : UU lzero
  dim-cube = type-UU-Fin k dim-cube-UU-Fin

  has-cardinality-dim-cube : has-cardinality k dim-cube
  has-cardinality-dim-cube = pr2 dim-cube-UU-Fin

  has-finite-cardinality-dim-cube : has-finite-cardinality dim-cube
  has-finite-cardinality-dim-cube =
    pair k (pr2 dim-cube-UU-Fin)

  is-finite-dim-cube : is-finite dim-cube
  is-finite-dim-cube =
    is-finite-has-finite-cardinality has-finite-cardinality-dim-cube

  axis-cube-UU-2 : dim-cube → UU-Fin lzero 2
  axis-cube-UU-2 = pr2 X

  axis-cube : dim-cube → UU lzero
  axis-cube d = type-UU-Fin 2 (axis-cube-UU-2 d)

  has-cardinality-axis-cube : (d : dim-cube) → has-cardinality 2 (axis-cube d)
  has-cardinality-axis-cube d = pr2 (axis-cube-UU-2 d)

  has-finite-cardinality-axis-cube :
    (d : dim-cube) → has-finite-cardinality (axis-cube d)
  has-finite-cardinality-axis-cube d =
    pair 2 (has-cardinality-axis-cube d)

  is-finite-axis-cube : (d : dim-cube) → is-finite (axis-cube d)
  is-finite-axis-cube d =
    is-finite-has-cardinality 2 (has-cardinality-axis-cube d)

  vertex-cube : UU lzero
  vertex-cube = (d : dim-cube) → axis-cube d
```

### The standard cube

```agda
dim-standard-cube-UU-Fin : (k : ℕ) → UU-Fin lzero k
dim-standard-cube-UU-Fin k = Fin-UU-Fin' k

dim-standard-cube : ℕ → UU lzero
dim-standard-cube k = type-UU-Fin k (dim-standard-cube-UU-Fin k)

axis-standard-cube-UU-Fin : (k : ℕ) → dim-standard-cube k → UU-Fin lzero 2
axis-standard-cube-UU-Fin k d = Fin-UU-Fin' 2

axis-standard-cube : (k : ℕ) → dim-standard-cube k → UU lzero
axis-standard-cube k d = type-UU-Fin 2 (axis-standard-cube-UU-Fin k d)

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
  (k : ℕ) (X : cube (succ-ℕ k)) (d : dim-cube (succ-ℕ k) X)
  (a : axis-cube (succ-ℕ k) X d) → cube k
face-cube k X d a =
  pair ( complement-point-UU-Fin k (pair (dim-cube-UU-Fin (succ-ℕ k) X) d))
       ( λ d' →
         axis-cube-UU-2 (succ-ℕ k) X
           ( inclusion-complement-point-UU-Fin k
             ( pair (dim-cube-UU-Fin (succ-ℕ k) X) d) d'))
```
