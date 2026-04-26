# The concrete quaternion group

```agda
module finite-group-theory.concrete-quaternion-group where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import univalent-combinatorics.complements-isolated-elements
open import univalent-combinatorics.cubes
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equivalences-cubes
```

</details>

## Definition

```agda
equiv-face-cube :
  (k : ℕ) (X Y : cube (succ-ℕ k)) (e : equiv-cube (succ-ℕ k) X Y)
  (d : dim-cube (succ-ℕ k) X) (a : axis-cube (succ-ℕ k) X d) →
  equiv-cube k
    ( face-cube k X d a)
    ( face-cube k Y
      ( map-dim-equiv-cube (succ-ℕ k) X Y e d)
      ( map-axis-equiv-cube (succ-ℕ k) X Y e d a))
equiv-face-cube k X Y e d a =
  pair
    ( equiv-complement-element-Type-With-Cardinality-ℕ k
      ( pair (dim-cube-Type-With-Cardinality-ℕ (succ-ℕ k) X) d)
      ( pair
        ( dim-cube-Type-With-Cardinality-ℕ (succ-ℕ k) Y)
        ( map-dim-equiv-cube (succ-ℕ k) X Y e d))
      ( dim-equiv-cube (succ-ℕ k) X Y e)
      ( refl))
    ( λ d' →
      ( equiv-tr
        ( axis-cube (succ-ℕ k) Y)
        ( inv
          ( natural-inclusion-equiv-complement-isolated-element
            ( dim-equiv-cube (succ-ℕ k) X Y e)
            ( pair d
              ( λ z →
                has-decidable-equality-has-cardinality-ℕ
                  ( succ-ℕ k)
                  ( has-cardinality-dim-cube (succ-ℕ k) X)
                  ( d)
                  ( z)))
            ( pair
              ( map-dim-equiv-cube (succ-ℕ k) X Y e d)
              ( λ z →
                has-decidable-equality-has-cardinality-ℕ
                  ( succ-ℕ k)
                  ( has-cardinality-dim-cube (succ-ℕ k) Y)
                  ( map-dim-equiv-cube (succ-ℕ k) X Y e d)
                  ( z)))
            ( refl)
            ( d')))) ∘e
      ( axis-equiv-cube (succ-ℕ k) X Y e
        ( inclusion-complement-element-Type-With-Cardinality-ℕ k
          ( pair (dim-cube-Type-With-Cardinality-ℕ (succ-ℕ k) X) d) d')))

cube-with-labeled-faces :
  (k : ℕ) → UU (lsuc lzero)
cube-with-labeled-faces k =
  Σ ( cube (succ-ℕ k))
    ( λ X →
      (d : dim-cube (succ-ℕ k) X) (a : axis-cube (succ-ℕ k) X d) →
      labeling-cube k (face-cube k X d a))

cube-cube-with-labeled-faces :
  (k : ℕ) → cube-with-labeled-faces k → cube (succ-ℕ k)
cube-cube-with-labeled-faces k X = pr1 X

labeling-faces-cube-with-labeled-faces :
  (k : ℕ) (X : cube-with-labeled-faces k)
  (d : dim-cube (succ-ℕ k) (cube-cube-with-labeled-faces k X))
  (a : axis-cube (succ-ℕ k) (cube-cube-with-labeled-faces k X) d) →
  labeling-cube k (face-cube k (cube-cube-with-labeled-faces k X) d a)
labeling-faces-cube-with-labeled-faces k X = pr2 X

equiv-cube-with-labeled-faces :
  {k : ℕ} (X Y : cube-with-labeled-faces k) → UU lzero
equiv-cube-with-labeled-faces {k} X Y =
  Σ ( equiv-cube (succ-ℕ k)
      ( cube-cube-with-labeled-faces k X)
      ( cube-cube-with-labeled-faces k Y))
    ( λ e → ( d : dim-cube (succ-ℕ k) (cube-cube-with-labeled-faces k X))
            ( a : axis-cube (succ-ℕ k) (cube-cube-with-labeled-faces k X) d) →
            htpy-equiv-cube k
              ( standard-cube k)
              ( face-cube k
                ( cube-cube-with-labeled-faces k Y)
                ( map-dim-equiv-cube (succ-ℕ k)
                  ( cube-cube-with-labeled-faces k X)
                  ( cube-cube-with-labeled-faces k Y)
                  ( e)
                  ( d))
                ( map-axis-equiv-cube (succ-ℕ k)
                  ( cube-cube-with-labeled-faces k X)
                  ( cube-cube-with-labeled-faces k Y)
                  e d a))
              ( comp-equiv-cube k
                ( standard-cube k)
                ( face-cube k (pr1 X) d a)
                ( face-cube k (pr1 Y)
                  ( map-dim-equiv-cube (succ-ℕ k) (pr1 X) (pr1 Y) e d)
                  ( map-axis-equiv-cube (succ-ℕ k) (pr1 X) (pr1 Y) e d a))
                ( equiv-face-cube k (pr1 X) (pr1 Y) e d a)
                ( labeling-faces-cube-with-labeled-faces k X d a))
              ( labeling-faces-cube-with-labeled-faces k Y
                ( map-dim-equiv-cube (succ-ℕ k)
                  ( cube-cube-with-labeled-faces k X)
                  ( cube-cube-with-labeled-faces k Y)
                  e d)
                ( map-axis-equiv-cube (succ-ℕ k)
                  ( cube-cube-with-labeled-faces k X)
                  ( cube-cube-with-labeled-faces k Y)
                  e d a)))
```
