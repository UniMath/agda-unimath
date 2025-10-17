# Equivalences of cubes

```agda
module univalent-combinatorics.equivalences-cubes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import univalent-combinatorics.cubes
open import univalent-combinatorics.finite-types
```

</details>

## Definitions

### Equivalences of cubes

```agda
equiv-cube : (k : ℕ) → cube k → cube k → UU lzero
equiv-cube k X Y =
  Σ ( (dim-cube k X) ≃ (dim-cube k Y))
    ( λ e →
      (x : dim-cube k X) → (axis-cube k X x) ≃ (axis-cube k Y (map-equiv e x)))

dim-equiv-cube :
  (k : ℕ) (X Y : cube k) → equiv-cube k X Y → dim-cube k X ≃ dim-cube k Y
dim-equiv-cube k X Y e = pr1 e

map-dim-equiv-cube :
  (k : ℕ) (X Y : cube k) → equiv-cube k X Y → dim-cube k X → dim-cube k Y
map-dim-equiv-cube k X Y e = map-equiv (dim-equiv-cube k X Y e)

axis-equiv-cube :
  (k : ℕ) (X Y : cube k) (e : equiv-cube k X Y) (d : dim-cube k X) →
  axis-cube k X d ≃ axis-cube k Y (map-dim-equiv-cube k X Y e d)
axis-equiv-cube k X Y e = pr2 e

map-axis-equiv-cube :
  (k : ℕ) (X Y : cube k) (e : equiv-cube k X Y) (d : dim-cube k X) →
  axis-cube k X d → axis-cube k Y (map-dim-equiv-cube k X Y e d)
map-axis-equiv-cube k X Y e d =
  map-equiv (axis-equiv-cube k X Y e d)

id-equiv-cube :
  (k : ℕ) (X : cube k) → equiv-cube k X X
id-equiv-cube k X = pair id-equiv (λ x → id-equiv)

equiv-eq-cube :
  (k : ℕ) {X Y : cube k} → X ＝ Y → equiv-cube k X Y
equiv-eq-cube k {X} refl = id-equiv-cube k X

is-torsorial-equiv-cube :
  (k : ℕ) (X : cube k) → is-torsorial (equiv-cube k X)
is-torsorial-equiv-cube k X =
  is-torsorial-Eq-structure
    ( is-torsorial-equiv-Type-With-Cardinality-ℕ
      { k = k}
      ( dim-cube-Type-With-Cardinality-ℕ k X))
    ( pair
      ( dim-cube-Type-With-Cardinality-ℕ k X)
      ( id-equiv-Type-With-Cardinality-ℕ
        { k = k}
        ( dim-cube-Type-With-Cardinality-ℕ k X)))
    ( is-torsorial-Eq-Π
      ( λ i →
        is-torsorial-equiv-Type-With-Cardinality-ℕ
          { k = 2}
          ( axis-cube-UU-2 k X i)))

is-equiv-equiv-eq-cube :
  (k : ℕ) (X Y : cube k) → is-equiv (equiv-eq-cube k {X} {Y})
is-equiv-equiv-eq-cube k X =
  fundamental-theorem-id
    ( is-torsorial-equiv-cube k X)
    ( λ Y → equiv-eq-cube k {X = X} {Y})

eq-equiv-cube :
  (k : ℕ) (X Y : cube k) → equiv-cube k X Y → X ＝ Y
eq-equiv-cube k X Y =
  map-inv-is-equiv (is-equiv-equiv-eq-cube k X Y)

comp-equiv-cube :
  (k : ℕ) (X Y Z : cube k) →
  equiv-cube k Y Z → equiv-cube k X Y → equiv-cube k X Z
comp-equiv-cube k X Y Z (pair dim-f axis-f) (pair dim-e axis-e) =
  pair (dim-f ∘e dim-e) (λ d → axis-f (map-equiv (dim-e) d) ∘e axis-e d)

htpy-equiv-cube :
  (k : ℕ) (X Y : cube k) (e f : equiv-cube k X Y) → UU lzero
htpy-equiv-cube k X Y e f =
  Σ ( map-dim-equiv-cube k X Y e ~ map-dim-equiv-cube k X Y f)
    ( λ H →
      ( d : dim-cube k X) →
      ( tr (axis-cube k Y) (H d) ∘ map-axis-equiv-cube k X Y e d) ~
      ( map-axis-equiv-cube k X Y f d))

refl-htpy-equiv-cube :
  (k : ℕ) (X Y : cube k) (e : equiv-cube k X Y) → htpy-equiv-cube k X Y e e
refl-htpy-equiv-cube k X Y e = pair refl-htpy (λ d → refl-htpy)

htpy-eq-equiv-cube :
  (k : ℕ) (X Y : cube k) (e f : equiv-cube k X Y) →
  e ＝ f → htpy-equiv-cube k X Y e f
htpy-eq-equiv-cube k X Y e .e refl = refl-htpy-equiv-cube k X Y e

is-torsorial-htpy-equiv-cube :
  (k : ℕ) (X Y : cube k) (e : equiv-cube k X Y) →
  is-torsorial (htpy-equiv-cube k X Y e)
is-torsorial-htpy-equiv-cube k X Y e =
  is-torsorial-Eq-structure

    ( is-torsorial-htpy-equiv (dim-equiv-cube k X Y e))
    ( pair (dim-equiv-cube k X Y e) refl-htpy)
    ( is-torsorial-Eq-Π
      ( λ d → is-torsorial-htpy-equiv (axis-equiv-cube k X Y e d)))

is-equiv-htpy-eq-equiv-cube :
  (k : ℕ) (X Y : cube k) (e f : equiv-cube k X Y) →
  is-equiv (htpy-eq-equiv-cube k X Y e f)
is-equiv-htpy-eq-equiv-cube k X Y e =
  fundamental-theorem-id
    ( is-torsorial-htpy-equiv-cube k X Y e)
    ( htpy-eq-equiv-cube k X Y e)

eq-htpy-equiv-cube :
  (k : ℕ) (X Y : cube k) (e f : equiv-cube k X Y) →
  htpy-equiv-cube k X Y e f → e ＝ f
eq-htpy-equiv-cube k X Y e f =
  map-inv-is-equiv (is-equiv-htpy-eq-equiv-cube k X Y e f)
```

### Labelings of cubes

```agda
labeling-cube : (k : ℕ) (X : cube k) → UU lzero
labeling-cube k X = equiv-cube k (standard-cube k) X
```
