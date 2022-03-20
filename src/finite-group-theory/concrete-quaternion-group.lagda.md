# The concrete quaternion group

```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-group-theory.concrete-quaternion-group where

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.complements-isolated-points
open import univalent-combinatorics.cubes
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equivalences-cubes
```

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
  {k : ℕ} (X Y : cube (succ-ℕ k)) (e : equiv-cube X Y) (d : dim-cube X)
  (a : axis-cube X d) →
  equiv-cube
    ( face-cube X d a)
    ( face-cube Y (map-dim-equiv-cube X Y e d) (map-axis-equiv-cube X Y e d a))
equiv-face-cube X Y e d a =
  pair
    ( equiv-complement-point-UU-Fin
      ( pair (dim-cube-UU-Fin X) d)
      ( pair (dim-cube-UU-Fin Y) (map-dim-equiv-cube X Y e d))
      ( dim-equiv-cube X Y e)
      ( refl))
    ( λ d' →
      ( equiv-tr
        ( axis-cube Y)
        ( inv
          ( natural-inclusion-equiv-complement-isolated-point
            ( dim-equiv-cube X Y e)
            ( pair d (λ z → has-decidable-equality-has-cardinality
                            ( has-cardinality-dim-cube X) d z))
            ( pair
              ( map-dim-equiv-cube X Y e d)
              ( λ z →
                has-decidable-equality-has-cardinality
                  ( has-cardinality-dim-cube Y)
                  ( map-dim-equiv-cube X Y e d)
                  ( z)))
            ( refl)
            ( d')))) ∘e
      ( axis-equiv-cube X Y e
        ( inclusion-complement-point-UU-Fin (pair (dim-cube-UU-Fin X) d) d')))

cube-with-labelled-faces :
  (k : ℕ) → UU (lsuc lzero)
cube-with-labelled-faces k =
  Σ ( cube (succ-ℕ k))
    ( λ X → (d : dim-cube X) (a : axis-cube X d) →
            labelling-cube (face-cube X d a))

cube-cube-with-labelled-faces :
  {k : ℕ} → cube-with-labelled-faces k → cube (succ-ℕ k)
cube-cube-with-labelled-faces X = pr1 X

labelling-faces-cube-with-labelled-faces :
  {k : ℕ} (X : cube-with-labelled-faces k)
  (d : dim-cube (cube-cube-with-labelled-faces X))
  (a : axis-cube (cube-cube-with-labelled-faces X) d) →
  labelling-cube (face-cube (cube-cube-with-labelled-faces X) d a)
labelling-faces-cube-with-labelled-faces X = pr2 X

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
  Σ ( equiv-cube ( cube-cube-with-labelled-faces X)
                 ( cube-cube-with-labelled-faces Y))
    ( λ e → ( d : dim-cube (cube-cube-with-labelled-faces X))
            ( a : axis-cube (cube-cube-with-labelled-faces X) d) →
            htpy-equiv-cube
              ( standard-cube k)
              ( face-cube
                ( cube-cube-with-labelled-faces Y)
                ( map-dim-equiv-cube
                  ( cube-cube-with-labelled-faces X)
                  ( cube-cube-with-labelled-faces Y)
                  e d)
                ( map-axis-equiv-cube
                  ( cube-cube-with-labelled-faces X)
                  ( cube-cube-with-labelled-faces Y)
                  e d a))
              ( comp-equiv-cube
                ( standard-cube k)
                ( face-cube (pr1 X) d a)
                ( face-cube (pr1 Y)
                  ( map-dim-equiv-cube (pr1 X) (pr1 Y) e d)
                  ( map-axis-equiv-cube (pr1 X) (pr1 Y) e d a))
                ( equiv-face-cube (pr1 X) (pr1 Y) e d a)
                ( labelling-faces-cube-with-labelled-faces X d a))
              ( labelling-faces-cube-with-labelled-faces Y
                ( map-dim-equiv-cube
                  ( cube-cube-with-labelled-faces X)
                  ( cube-cube-with-labelled-faces Y)
                  e d)
                ( map-axis-equiv-cube
                  ( cube-cube-with-labelled-faces X)
                  ( cube-cube-with-labelled-faces Y)
                  e d a)))
```
