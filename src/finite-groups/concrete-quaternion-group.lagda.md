---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-groups.concrete-quaternion-group where

open import groups public

open import foundation
open import univalent-combinatorics
open import univalent-foundations

open import univalent-foundations.isolated-points

--------------------------------------------------------------------------------

-- We define the concrete group Q8

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

equiv-cube : {k : ℕ} → cube k → cube k → UU lzero
equiv-cube {k} X Y =
  Σ ( (dim-cube X) ≃ (dim-cube Y))
    ( λ e → (x : dim-cube X) → (axis-cube X x) ≃ (axis-cube Y (map-equiv e x)))

dim-equiv-cube :
  {k : ℕ} (X Y : cube k) → equiv-cube X Y → dim-cube X ≃ dim-cube Y
dim-equiv-cube X Y e = pr1 e

map-dim-equiv-cube :
  {k : ℕ} (X Y : cube k) → equiv-cube X Y → dim-cube X → dim-cube Y
map-dim-equiv-cube X Y e = map-equiv (dim-equiv-cube X Y e)

axis-equiv-cube :
  {k : ℕ} (X Y : cube k) (e : equiv-cube X Y) (d : dim-cube X) →
  axis-cube X d ≃ axis-cube Y (map-dim-equiv-cube X Y e d)
axis-equiv-cube X Y e = pr2 e

map-axis-equiv-cube :
  {k : ℕ} (X Y : cube k) (e : equiv-cube X Y) (d : dim-cube X) →
  axis-cube X d → axis-cube Y (map-dim-equiv-cube X Y e d)
map-axis-equiv-cube X Y e d =
  map-equiv (axis-equiv-cube X Y e d)

id-equiv-cube :
  {k : ℕ} (X : cube k) → equiv-cube X X
id-equiv-cube X = pair id-equiv (λ x → id-equiv)

equiv-eq-cube :
  {k : ℕ} {X Y : cube k} → Id X Y → equiv-cube X Y
equiv-eq-cube {k} {X} refl = id-equiv-cube X

is-contr-total-equiv-cube :
  {k : ℕ} (X : cube k) → is-contr (Σ (cube k) (equiv-cube X))
is-contr-total-equiv-cube X =
  is-contr-total-Eq-structure
    ( λ D (A : type-UU-Fin D → UU-Fin 2)
          (e : equiv-UU-Fin (dim-cube-UU-Fin X) D) →
          (i : dim-cube X) → axis-cube X i ≃ pr1 (A (map-equiv e i)))
    ( is-contr-total-equiv-UU-Fin (dim-cube-UU-Fin X))
    ( pair (dim-cube-UU-Fin X) (id-equiv-UU-Fin (dim-cube-UU-Fin X)))
    ( is-contr-total-Eq-Π
      ( λ i (A : UU-Fin 2) → equiv-UU-Fin (axis-cube-UU-2 X i) A)
      ( λ i → is-contr-total-equiv-UU-Fin (axis-cube-UU-2 X i)))

is-equiv-equiv-eq-cube :
  {k : ℕ} (X Y : cube k) → is-equiv (equiv-eq-cube {k} {X} {Y})
is-equiv-equiv-eq-cube X =
  fundamental-theorem-id X
    ( id-equiv-cube X)
    ( is-contr-total-equiv-cube X)
    ( λ Y → equiv-eq-cube {X = X} {Y})

eq-equiv-cube :
  {k : ℕ} (X Y : cube k) → equiv-cube X Y → Id X Y
eq-equiv-cube X Y =
  map-inv-is-equiv (is-equiv-equiv-eq-cube X Y)

comp-equiv-cube :
  {k : ℕ} (X Y Z : cube k) → equiv-cube Y Z → equiv-cube X Y → equiv-cube X Z
comp-equiv-cube X Y Z (pair dim-f axis-f) (pair dim-e axis-e) =
  pair (dim-f ∘e dim-e) (λ d → axis-f (map-equiv (dim-e) d) ∘e axis-e d)

htpy-equiv-cube :
  {k : ℕ} (X Y : cube k) (e f : equiv-cube X Y) → UU lzero
htpy-equiv-cube X Y e f =
  Σ ( map-dim-equiv-cube X Y e ~ map-dim-equiv-cube X Y f)
    ( λ H → (d : dim-cube X) →
            ( tr (axis-cube Y) (H d) ∘ map-axis-equiv-cube X Y e d) ~
            ( map-axis-equiv-cube X Y f d))

refl-htpy-equiv-cube :
  {k : ℕ} (X Y : cube k) (e : equiv-cube X Y) → htpy-equiv-cube X Y e e
refl-htpy-equiv-cube X Y e = pair refl-htpy (λ d → refl-htpy)

htpy-eq-equiv-cube :
  {k : ℕ} (X Y : cube k) (e f : equiv-cube X Y) →
  Id e f → htpy-equiv-cube X Y e f
htpy-eq-equiv-cube X Y e .e refl = refl-htpy-equiv-cube X Y e

is-contr-total-htpy-equiv-cube :
  {k : ℕ} (X Y : cube k) (e : equiv-cube X Y) →
  is-contr (Σ (equiv-cube X Y) (htpy-equiv-cube X Y e))
is-contr-total-htpy-equiv-cube X Y e =
  is-contr-total-Eq-structure
    ( λ α β H →
      ( d : dim-cube X) →
      ( tr (axis-cube Y) (H d) ∘ map-axis-equiv-cube X Y e d) ~
      ( map-equiv (β d)))
    ( is-contr-total-htpy-equiv (dim-equiv-cube X Y e))
    ( pair (dim-equiv-cube X Y e) refl-htpy)
    ( is-contr-total-Eq-Π
      ( λ d β → htpy-equiv (axis-equiv-cube X Y e d) β)
      ( λ d → is-contr-total-htpy-equiv (axis-equiv-cube X Y e d)))

is-equiv-htpy-eq-equiv-cube :
  {k : ℕ} (X Y : cube k) (e f : equiv-cube X Y) →
  is-equiv (htpy-eq-equiv-cube X Y e f)
is-equiv-htpy-eq-equiv-cube X Y e =
  fundamental-theorem-id e
    ( refl-htpy-equiv-cube X Y e)
    ( is-contr-total-htpy-equiv-cube X Y e)
    ( htpy-eq-equiv-cube X Y e)

eq-htpy-equiv-cube :
  {k : ℕ} (X Y : cube k) (e f : equiv-cube X Y) →
  htpy-equiv-cube X Y e f → Id e f
eq-htpy-equiv-cube X Y e f =
  map-inv-is-equiv (is-equiv-htpy-eq-equiv-cube X Y e f)

vertex-cube : {k : ℕ} (X : cube k) → UU lzero
vertex-cube X = (d : dim-cube X) → axis-cube X d

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

labelling-cube : {k : ℕ} (X : cube k) → UU lzero
labelling-cube {k} X = equiv-cube (standard-cube k) X

orientation-cube : {k : ℕ} → cube k → UU (lzero)
orientation-cube {k} X =
  Σ ( vertex-cube X → Fin 2)
    ( λ h →
      ( x y : vertex-cube X) →
        Id ( iterate
             ( number-of-elements-is-finite
               ( is-finite-Σ
                 ( is-finite-dim-cube X)
                 ( λ d →
                   is-finite-function-type
                     ( is-finite-eq
                       ( has-decidable-equality-is-finite
                         ( is-finite-axis-cube X d))
                     { x d}
                     { y d})
                     ( is-finite-empty))))
             ( succ-Fin)
             ( h x))
           ( h y))

face-cube :
  {k : ℕ} (X : cube (succ-ℕ k)) (d : dim-cube X) (a : axis-cube X d) → cube k
face-cube X d a =
  pair ( complement-point-UU-Fin (pair (dim-cube-UU-Fin X) d))
       ( λ d' →
         axis-cube-UU-2 X
           ( inclusion-complement-point-UU-Fin
             ( pair (dim-cube-UU-Fin X) d) d'))

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
