# Cubes

```agda
module univalent-combinatorics.cubes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.complements-isolated-elements
open import univalent-combinatorics.finite-types
```

</details>

## Definitions

### Cubes

```agda
cube : ℕ → UU (lsuc lzero)
cube k = Σ (Type-With-Finite-Cardinality lzero k) (λ X → type-Type-With-Finite-Cardinality k X → Type-With-Finite-Cardinality lzero 2)

module _
  (k : ℕ) (X : cube k)
  where

  dim-cube-Type-With-Finite-Cardinality : Type-With-Finite-Cardinality lzero k
  dim-cube-Type-With-Finite-Cardinality = pr1 X

  dim-cube : UU lzero
  dim-cube = type-Type-With-Finite-Cardinality k dim-cube-Type-With-Finite-Cardinality

  has-cardinality-dim-cube : has-cardinality k dim-cube
  has-cardinality-dim-cube = pr2 dim-cube-Type-With-Finite-Cardinality

  has-finite-cardinality-dim-cube : has-finite-cardinality dim-cube
  has-finite-cardinality-dim-cube =
    pair k (pr2 dim-cube-Type-With-Finite-Cardinality)

  is-finite-dim-cube : is-finite dim-cube
  is-finite-dim-cube =
    is-finite-has-finite-cardinality has-finite-cardinality-dim-cube

  axis-cube-UU-2 : dim-cube → Type-With-Finite-Cardinality lzero 2
  axis-cube-UU-2 = pr2 X

  axis-cube : dim-cube → UU lzero
  axis-cube d = type-Type-With-Finite-Cardinality 2 (axis-cube-UU-2 d)

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
dim-standard-cube-Type-With-Finite-Cardinality : (k : ℕ) → Type-With-Finite-Cardinality lzero k
dim-standard-cube-Type-With-Finite-Cardinality k = Fin-Type-With-Finite-Cardinality k

dim-standard-cube : ℕ → UU lzero
dim-standard-cube k = type-Type-With-Finite-Cardinality k (dim-standard-cube-Type-With-Finite-Cardinality k)

axis-standard-cube-Type-With-Finite-Cardinality : (k : ℕ) → dim-standard-cube k → Type-With-Finite-Cardinality lzero 2
axis-standard-cube-Type-With-Finite-Cardinality k d = Fin-Type-With-Finite-Cardinality 2

axis-standard-cube : (k : ℕ) → dim-standard-cube k → UU lzero
axis-standard-cube k d = type-Type-With-Finite-Cardinality 2 (axis-standard-cube-Type-With-Finite-Cardinality k d)

standard-cube : (k : ℕ) → cube k
standard-cube k =
  pair (dim-standard-cube-Type-With-Finite-Cardinality k) (axis-standard-cube-Type-With-Finite-Cardinality k)

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
pr1 (face-cube k X d a) =
  complement-element-Type-With-Finite-Cardinality k (pair (dim-cube-Type-With-Finite-Cardinality (succ-ℕ k) X) d)
pr2 (face-cube k X d a) d' =
  axis-cube-UU-2 (succ-ℕ k) X
    ( inclusion-complement-element-Type-With-Finite-Cardinality k
      ( pair (dim-cube-Type-With-Finite-Cardinality (succ-ℕ k) X) d) d')
```
