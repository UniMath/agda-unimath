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
open import foundation.isolated-points
open import foundation.universe-levels

open import univalent-combinatorics.complements-isolated-points
open import univalent-combinatorics.cubes
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equivalences-cubes
```

</details>

## Definition

```agda
{-
equiv-face-standard-cube :
  {k : ℕ} (d : dim-standard-cube (succ-ℕ k))
  (a : axis-standard-cube (succ-ℕ k) d) →
  equiv-cube (face-cube (standard-cube (succ-ℕ k)) d a) (standard-cube k)
equiv-face-standard-cube {zero-ℕ} d a =
  pair
    {! is-equiv-is-empty!}
    {!!}
equiv-face-standard-cube {succ-ℕ k} d a = {!!}
-}

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
    ( equiv-complement-point-UU-Fin k
      ( pair (dim-cube-UU-Fin (succ-ℕ k) X) d)
      ( pair (dim-cube-UU-Fin (succ-ℕ k) Y) (map-dim-equiv-cube (succ-ℕ k) X Y e d))
      ( dim-equiv-cube (succ-ℕ k) X Y e)
      ( refl))
    ( λ d' →
      ( equiv-tr
        ( axis-cube (succ-ℕ k) Y)
        ( inv
          ( natural-inclusion-equiv-complement-isolated-point
            ( dim-equiv-cube (succ-ℕ k) X Y e)
            ( pair d
              ( λ z →
                has-decidable-equality-has-cardinality
                  ( succ-ℕ k)
                  ( has-cardinality-dim-cube (succ-ℕ k) X)
                  ( d)
                  ( z)))
            ( pair
              ( map-dim-equiv-cube (succ-ℕ k) X Y e d)
              ( λ z →
                has-decidable-equality-has-cardinality
                  ( succ-ℕ k)
                  ( has-cardinality-dim-cube (succ-ℕ k) Y)
                  ( map-dim-equiv-cube (succ-ℕ k) X Y e d)
                  ( z)))
            ( refl)
            ( d')))) ∘e
      ( axis-equiv-cube (succ-ℕ k) X Y e
        ( inclusion-complement-point-UU-Fin k
          ( pair (dim-cube-UU-Fin (succ-ℕ k) X) d) d')))

cube-with-labelled-faces :
  (k : ℕ) → UU (lsuc lzero)
cube-with-labelled-faces k =
  Σ ( cube (succ-ℕ k))
    ( λ X →
      (d : dim-cube (succ-ℕ k) X) (a : axis-cube (succ-ℕ k) X d) →
      labelling-cube k (face-cube k X d a))

cube-cube-with-labelled-faces :
  (k : ℕ) → cube-with-labelled-faces k → cube (succ-ℕ k)
cube-cube-with-labelled-faces k X = pr1 X

labelling-faces-cube-with-labelled-faces :
  (k : ℕ) (X : cube-with-labelled-faces k)
  (d : dim-cube (succ-ℕ k) (cube-cube-with-labelled-faces k X))
  (a : axis-cube (succ-ℕ k) (cube-cube-with-labelled-faces k X) d) →
  labelling-cube k (face-cube k (cube-cube-with-labelled-faces k X) d a)
labelling-faces-cube-with-labelled-faces k X = pr2 X

{-
standard-cube-with-labelled-faces :
  (k : ℕ) → cube-with-labelled-faces k
standard-cube-with-labelled-faces k =
  pair ( standard-cube (succ-ℕ k))
       ( λ d a → {!!})
-}

equiv-cube-with-labelled-faces :
  {k : ℕ} (X Y : cube-with-labelled-faces k) → UU lzero
equiv-cube-with-labelled-faces {k} X Y =
  Σ ( equiv-cube (succ-ℕ k)
      ( cube-cube-with-labelled-faces k X)
      ( cube-cube-with-labelled-faces k Y))
    ( λ e → ( d : dim-cube (succ-ℕ k) (cube-cube-with-labelled-faces k X))
            ( a : axis-cube (succ-ℕ k) (cube-cube-with-labelled-faces k X) d) →
            htpy-equiv-cube k
              ( standard-cube k)
              ( face-cube k
                ( cube-cube-with-labelled-faces k Y)
                ( map-dim-equiv-cube (succ-ℕ k)
                  ( cube-cube-with-labelled-faces k X)
                  ( cube-cube-with-labelled-faces k Y)
                  ( e)
                  ( d))
                ( map-axis-equiv-cube (succ-ℕ k)
                  ( cube-cube-with-labelled-faces k X)
                  ( cube-cube-with-labelled-faces k Y)
                  e d a))
              ( comp-equiv-cube k
                ( standard-cube k)
                ( face-cube k (pr1 X) d a)
                ( face-cube k (pr1 Y)
                  ( map-dim-equiv-cube (succ-ℕ k) (pr1 X) (pr1 Y) e d)
                  ( map-axis-equiv-cube (succ-ℕ k) (pr1 X) (pr1 Y) e d a))
                ( equiv-face-cube k (pr1 X) (pr1 Y) e d a)
                ( labelling-faces-cube-with-labelled-faces k X d a))
              ( labelling-faces-cube-with-labelled-faces k Y
                ( map-dim-equiv-cube (succ-ℕ k)
                  ( cube-cube-with-labelled-faces k X)
                  ( cube-cube-with-labelled-faces k Y)
                  e d)
                ( map-axis-equiv-cube (succ-ℕ k)
                  ( cube-cube-with-labelled-faces k X)
                  ( cube-cube-with-labelled-faces k Y)
                  e d a)))
```
