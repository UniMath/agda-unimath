# Cones over inverse sequential diagrams

```agda
module foundation.cones-over-inverse-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.inverse-sequential-diagrams
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A **cone over an
[inverse sequential diagram](foundation.inverse-sequential-diagrams.md) `A` with
domain `X`** is a [sequence](lists.dependent-sequences.md) of functions from `X`
into the sequence of types of `A` such that the triangles

```text
     X
    / \
   /   \
  ∨     ∨
 Aₙ₊₁ -> Aₙ
```

[commute](foundation-core.commuting-triangles-of-maps.md) for all `n : ℕ`.

## Definitions

### Cones over inverse sequential diagrams

```agda
module _
  {l1 : Level} (A : inverse-sequential-diagram l1)
  where

  cone-inverse-sequential-diagram : {l2 : Level} → UU l2 → UU (l1 ⊔ l2)
  cone-inverse-sequential-diagram X =
    Σ ( (n : ℕ) → X → family-inverse-sequential-diagram A n)
      ( λ f →
        (n : ℕ) →
        coherence-triangle-maps
          ( f n)
          ( map-inverse-sequential-diagram A n)
          ( f (succ-ℕ n)))

  map-cone-inverse-sequential-diagram :
    {l2 : Level} {X : UU l2} → cone-inverse-sequential-diagram X →
    (n : ℕ) → X → family-inverse-sequential-diagram A n
  map-cone-inverse-sequential-diagram = pr1

  coherence-cone-inverse-sequential-diagram :
    {l2 : Level} {X : UU l2} (c : cone-inverse-sequential-diagram X) (n : ℕ) →
    coherence-triangle-maps
      ( map-cone-inverse-sequential-diagram c n)
      ( map-inverse-sequential-diagram A n)
      ( map-cone-inverse-sequential-diagram c (succ-ℕ n))
  coherence-cone-inverse-sequential-diagram = pr2
```

### Identifications of cones over inverse sequential diagrams of types

```agda
module _
  {l1 l2 : Level} (A : inverse-sequential-diagram l1) {X : UU l2}
  where

  coherence-htpy-cone-inverse-sequential-diagram :
    (c c' : cone-inverse-sequential-diagram A X) →
    ( (n : ℕ) →
      map-cone-inverse-sequential-diagram A c n ~
      map-cone-inverse-sequential-diagram A c' n) →
    UU (l1 ⊔ l2)
  coherence-htpy-cone-inverse-sequential-diagram c c' H =
    (n : ℕ) →
    ( coherence-cone-inverse-sequential-diagram A c n ∙h
      map-inverse-sequential-diagram A n ·l H (succ-ℕ n)) ~
    ( H n ∙h coherence-cone-inverse-sequential-diagram A c' n)

  htpy-cone-inverse-sequential-diagram :
    cone-inverse-sequential-diagram A X →
    cone-inverse-sequential-diagram A X →
    UU (l1 ⊔ l2)
  htpy-cone-inverse-sequential-diagram c c' =
    Σ ( (n : ℕ) →
        map-cone-inverse-sequential-diagram A c n ~
        map-cone-inverse-sequential-diagram A c' n)
      ( coherence-htpy-cone-inverse-sequential-diagram c c')

  refl-htpy-cone-inverse-sequential-diagram :
    (c : cone-inverse-sequential-diagram A X) →
    htpy-cone-inverse-sequential-diagram c c
  pr1 (refl-htpy-cone-inverse-sequential-diagram c) n = refl-htpy
  pr2 (refl-htpy-cone-inverse-sequential-diagram c) n = right-unit-htpy

  htpy-eq-cone-inverse-sequential-diagram :
    (c c' : cone-inverse-sequential-diagram A X) →
    c ＝ c' → htpy-cone-inverse-sequential-diagram c c'
  htpy-eq-cone-inverse-sequential-diagram c .c refl =
    refl-htpy-cone-inverse-sequential-diagram c

  is-torsorial-htpy-cone-inverse-sequential-diagram :
    (c : cone-inverse-sequential-diagram A X) →
    is-torsorial (htpy-cone-inverse-sequential-diagram c)
  is-torsorial-htpy-cone-inverse-sequential-diagram c =
    is-torsorial-Eq-structure
      ( is-torsorial-binary-htpy (map-cone-inverse-sequential-diagram A c))
      ( map-cone-inverse-sequential-diagram A c , (λ n → refl-htpy))
      ( is-torsorial-Eq-Π
        ( λ n →
          is-torsorial-htpy
            ( coherence-cone-inverse-sequential-diagram A c n ∙h refl-htpy)))

  is-equiv-htpy-eq-cone-inverse-sequential-diagram :
    (c c' : cone-inverse-sequential-diagram A X) →
    is-equiv (htpy-eq-cone-inverse-sequential-diagram c c')
  is-equiv-htpy-eq-cone-inverse-sequential-diagram c =
    fundamental-theorem-id
      ( is-torsorial-htpy-cone-inverse-sequential-diagram c)
      ( htpy-eq-cone-inverse-sequential-diagram c)

  extensionality-cone-inverse-sequential-diagram :
    (c c' : cone-inverse-sequential-diagram A X) →
    (c ＝ c') ≃ htpy-cone-inverse-sequential-diagram c c'
  pr1 (extensionality-cone-inverse-sequential-diagram c c') =
    htpy-eq-cone-inverse-sequential-diagram c c'
  pr2 (extensionality-cone-inverse-sequential-diagram c c') =
    is-equiv-htpy-eq-cone-inverse-sequential-diagram c c'

  eq-htpy-cone-inverse-sequential-diagram :
    (c c' : cone-inverse-sequential-diagram A X) →
    htpy-cone-inverse-sequential-diagram c c' → c ＝ c'
  eq-htpy-cone-inverse-sequential-diagram c c' =
    map-inv-equiv (extensionality-cone-inverse-sequential-diagram c c')
```

### Precomposing cones over inverse sequential diagrams with a map

```agda
module _
  {l1 l2 l3 : Level} (A : inverse-sequential-diagram l1) {X : UU l2} {Y : UU l3}
  where

  cone-map-inverse-sequential-diagram :
    cone-inverse-sequential-diagram A X →
    (Y → X) → cone-inverse-sequential-diagram A Y
  pr1 (cone-map-inverse-sequential-diagram c f) n x =
    map-cone-inverse-sequential-diagram A c n (f x)
  pr2 (cone-map-inverse-sequential-diagram c f) n x =
    coherence-cone-inverse-sequential-diagram A c n (f x)
```

### Postcomposition cones over postcomposition inverse sequential diagrams

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1) (A : inverse-sequential-diagram l2)
  {Y : UU l3} (c : cone-inverse-sequential-diagram A Y)
  where

  cone-postcomp-inverse-sequential-diagram :
    cone-inverse-sequential-diagram
      ( postcomp-inverse-sequential-diagram X A)
      ( X → Y)
  pr1 cone-postcomp-inverse-sequential-diagram n g x =
    map-cone-inverse-sequential-diagram A c n (g x)
  pr2 cone-postcomp-inverse-sequential-diagram n g =
    eq-htpy (λ x → coherence-cone-inverse-sequential-diagram A c n (g x))
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
