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
cube k =
  Σ ( Type-With-Cardinality-ℕ lzero k)
    ( λ X → type-Type-With-Cardinality-ℕ k X →
      Type-With-Cardinality-ℕ lzero 2)

module _
  (k : ℕ) (X : cube k)
  where

  dim-cube-Type-With-Cardinality-ℕ : Type-With-Cardinality-ℕ lzero k
  dim-cube-Type-With-Cardinality-ℕ = pr1 X

  dim-cube : UU lzero
  dim-cube =
    type-Type-With-Cardinality-ℕ k dim-cube-Type-With-Cardinality-ℕ

  has-cardinality-dim-cube : has-cardinality-ℕ k dim-cube
  has-cardinality-dim-cube = pr2 dim-cube-Type-With-Cardinality-ℕ

  has-finite-cardinality-dim-cube : has-finite-cardinality dim-cube
  has-finite-cardinality-dim-cube =
    pair k (pr2 dim-cube-Type-With-Cardinality-ℕ)

  is-finite-dim-cube : is-finite dim-cube
  is-finite-dim-cube =
    is-finite-has-finite-cardinality has-finite-cardinality-dim-cube

  axis-cube-UU-2 : dim-cube → Type-With-Cardinality-ℕ lzero 2
  axis-cube-UU-2 = pr2 X

  axis-cube : dim-cube → UU lzero
  axis-cube d = type-Type-With-Cardinality-ℕ 2 (axis-cube-UU-2 d)

  has-cardinality-axis-cube : (d : dim-cube) → has-cardinality-ℕ 2 (axis-cube d)
  has-cardinality-axis-cube d = pr2 (axis-cube-UU-2 d)

  has-finite-cardinality-axis-cube :
    (d : dim-cube) → has-finite-cardinality (axis-cube d)
  has-finite-cardinality-axis-cube d =
    pair 2 (has-cardinality-axis-cube d)

  is-finite-axis-cube : (d : dim-cube) → is-finite (axis-cube d)
  is-finite-axis-cube d =
    is-finite-has-cardinality-ℕ 2 (has-cardinality-axis-cube d)

  vertex-cube : UU lzero
  vertex-cube = (d : dim-cube) → axis-cube d
```

### The standard cube

```agda
dim-standard-cube-Type-With-Cardinality-ℕ :
  (k : ℕ) → Type-With-Cardinality-ℕ lzero k
dim-standard-cube-Type-With-Cardinality-ℕ k =
  Fin-Type-With-Cardinality-ℕ k

dim-standard-cube : ℕ → UU lzero
dim-standard-cube k =
  type-Type-With-Cardinality-ℕ k
    ( dim-standard-cube-Type-With-Cardinality-ℕ k)

axis-standard-cube-Type-With-Cardinality-ℕ :
  (k : ℕ) → dim-standard-cube k → Type-With-Cardinality-ℕ lzero 2
axis-standard-cube-Type-With-Cardinality-ℕ k d =
  Fin-Type-With-Cardinality-ℕ 2

axis-standard-cube : (k : ℕ) → dim-standard-cube k → UU lzero
axis-standard-cube k d =
  type-Type-With-Cardinality-ℕ 2
    ( axis-standard-cube-Type-With-Cardinality-ℕ k d)

standard-cube : (k : ℕ) → cube k
standard-cube k =
  ( dim-standard-cube-Type-With-Cardinality-ℕ k) ,
  ( axis-standard-cube-Type-With-Cardinality-ℕ k)

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
  complement-element-Type-With-Cardinality-ℕ k
    ( pair (dim-cube-Type-With-Cardinality-ℕ (succ-ℕ k) X) d)
pr2 (face-cube k X d a) d' =
  axis-cube-UU-2 (succ-ℕ k) X
    ( inclusion-complement-element-Type-With-Cardinality-ℕ k
      ( pair (dim-cube-Type-With-Cardinality-ℕ (succ-ℕ k) X) d) d')
```
