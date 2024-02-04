# Morphisms of inverse sequential diagrams of types

```agda
module foundation.morphisms-inverse-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.dependent-inverse-sequential-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.inverse-sequential-diagrams
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A **morphism of inverse sequential diagrams** `A → B` is a commuting diagram of
the form

```text
  ⋯ ----> Aₙ₊₁ ----> Aₙ ----> ⋯ ----> A₁ ----> A₀
           |         |       |       |        |
  ⋯        |         |       ⋯       |        |
           v         v       v       v        v
  ⋯ ----> Bₙ₊₁ ----> Bₙ ----> ⋯ ----> B₁ ----> B₀.
```

## Definitions

### Morphisms of inverse sequential diagrams of types

```agda
naturality-hom-inverse-sequential-diagram :
  {l1 l2 : Level}
  (A : inverse-sequential-diagram l1)
  (B : inverse-sequential-diagram l2)
  (h :
    (n : ℕ) →
    family-inverse-sequential-diagram A n →
    family-inverse-sequential-diagram B n)
  (n : ℕ) → UU (l1 ⊔ l2)
naturality-hom-inverse-sequential-diagram A B =
  naturality-section-dependent-inverse-sequential-diagram A
    ( const-dependent-inverse-sequential-diagram A B)

hom-inverse-sequential-diagram :
  {l1 l2 : Level}
  (A : inverse-sequential-diagram l1)
  (B : inverse-sequential-diagram l2) →
  UU (l1 ⊔ l2)
hom-inverse-sequential-diagram A B =
  section-dependent-inverse-sequential-diagram A
    ( const-dependent-inverse-sequential-diagram A B)

module _
  {l1 l2 : Level}
  (A : inverse-sequential-diagram l1)
  (B : inverse-sequential-diagram l2)
  where

  map-hom-inverse-sequential-diagram :
    hom-inverse-sequential-diagram A B → (n : ℕ) →
    family-inverse-sequential-diagram A n →
    family-inverse-sequential-diagram B n
  map-hom-inverse-sequential-diagram =
    map-section-dependent-inverse-sequential-diagram A
      ( const-dependent-inverse-sequential-diagram A B)

  naturality-map-hom-inverse-sequential-diagram :
    (f : hom-inverse-sequential-diagram A B) (n : ℕ) →
    naturality-hom-inverse-sequential-diagram A B
      ( map-hom-inverse-sequential-diagram f)
      ( n)
  naturality-map-hom-inverse-sequential-diagram =
    naturality-map-section-dependent-inverse-sequential-diagram A
      ( const-dependent-inverse-sequential-diagram A B)
```

### Identity morphism on inverse sequential diagrams of types

```agda
id-hom-inverse-sequential-diagram :
  {l : Level} (A : inverse-sequential-diagram l) →
  hom-inverse-sequential-diagram A A
pr1 (id-hom-inverse-sequential-diagram A) n = id
pr2 (id-hom-inverse-sequential-diagram A) n = refl-htpy
```

### Composition of morphisms of inverse sequential diagrams of types

```agda
map-comp-hom-inverse-sequential-diagram :
  {l : Level} (A B C : inverse-sequential-diagram l) →
  hom-inverse-sequential-diagram B C → hom-inverse-sequential-diagram A B →
  (n : ℕ) →
  family-inverse-sequential-diagram A n → family-inverse-sequential-diagram C n
map-comp-hom-inverse-sequential-diagram A B C g f n =
  map-hom-inverse-sequential-diagram B C g n ∘
  map-hom-inverse-sequential-diagram A B f n

naturality-comp-hom-inverse-sequential-diagram :
  {l : Level} (A B C : inverse-sequential-diagram l)
  (g : hom-inverse-sequential-diagram B C)
  (f : hom-inverse-sequential-diagram A B)
  (n : ℕ) →
  naturality-hom-inverse-sequential-diagram A C
    ( map-comp-hom-inverse-sequential-diagram A B C g f)
    ( n)
naturality-comp-hom-inverse-sequential-diagram A B C g f n x =
  ( ap
    ( map-hom-inverse-sequential-diagram B C g n)
    ( naturality-map-hom-inverse-sequential-diagram A B f n x)) ∙
  ( naturality-map-hom-inverse-sequential-diagram B C g n
    ( map-hom-inverse-sequential-diagram A B f (succ-ℕ n) x))

comp-hom-inverse-sequential-diagram :
  {l : Level} (A B C : inverse-sequential-diagram l) →
  hom-inverse-sequential-diagram B C →
  hom-inverse-sequential-diagram A B →
  hom-inverse-sequential-diagram A C
pr1 (comp-hom-inverse-sequential-diagram A B C g f) =
  map-comp-hom-inverse-sequential-diagram A B C g f
pr2 (comp-hom-inverse-sequential-diagram A B C g f) =
  naturality-comp-hom-inverse-sequential-diagram A B C g f
```

## Properties

### Characterization of equality of morphisms of inverse sequential diagrams of types

```agda
module _
  {l1 l2 : Level}
  (A : inverse-sequential-diagram l1)
  (B : inverse-sequential-diagram l2)
  where

  coherence-htpy-hom-inverse-sequential-diagram :
    (f g : hom-inverse-sequential-diagram A B) →
    ((n : ℕ) →
      map-hom-inverse-sequential-diagram A B f n ~
      map-hom-inverse-sequential-diagram A B g n) →
    (n : ℕ) → UU (l1 ⊔ l2)
  coherence-htpy-hom-inverse-sequential-diagram f g H n =
    ( naturality-map-hom-inverse-sequential-diagram A B f n ∙h
      map-inverse-sequential-diagram B n ·l H (succ-ℕ n)) ~
    ( H n ·r map-inverse-sequential-diagram A n ∙h
      naturality-map-hom-inverse-sequential-diagram A B g n)

  htpy-hom-inverse-sequential-diagram :
    (f g : hom-inverse-sequential-diagram A B) → UU (l1 ⊔ l2)
  htpy-hom-inverse-sequential-diagram f g =
    Σ ( (n : ℕ) →
        map-hom-inverse-sequential-diagram A B f n ~
        map-hom-inverse-sequential-diagram A B g n)
      ( λ H → (n : ℕ) → coherence-htpy-hom-inverse-sequential-diagram f g H n)

  refl-htpy-hom-inverse-sequential-diagram :
    (f : hom-inverse-sequential-diagram A B) →
    htpy-hom-inverse-sequential-diagram f f
  pr1 (refl-htpy-hom-inverse-sequential-diagram f) n = refl-htpy
  pr2 (refl-htpy-hom-inverse-sequential-diagram f) n = right-unit-htpy

  htpy-eq-hom-inverse-sequential-diagram :
    (f g : hom-inverse-sequential-diagram A B) → f ＝ g →
    htpy-hom-inverse-sequential-diagram f g
  htpy-eq-hom-inverse-sequential-diagram f .f refl =
    refl-htpy-hom-inverse-sequential-diagram f

  is-torsorial-htpy-hom-inverse-sequential-diagram :
    (f : hom-inverse-sequential-diagram A B) →
    is-torsorial (htpy-hom-inverse-sequential-diagram f)
  is-torsorial-htpy-hom-inverse-sequential-diagram f =
    is-torsorial-Eq-structure
      ( is-torsorial-binary-htpy (map-hom-inverse-sequential-diagram A B f))
      ( map-hom-inverse-sequential-diagram A B f ,
        refl-binary-htpy (map-hom-inverse-sequential-diagram A B f))
      ( is-torsorial-Eq-Π
        ( λ n →
          is-torsorial-htpy
            ( naturality-map-hom-inverse-sequential-diagram A B f n ∙h
              refl-htpy)))

  is-equiv-htpy-eq-hom-inverse-sequential-diagram :
    (f g : hom-inverse-sequential-diagram A B) →
    is-equiv (htpy-eq-hom-inverse-sequential-diagram f g)
  is-equiv-htpy-eq-hom-inverse-sequential-diagram f =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-inverse-sequential-diagram f)
      ( htpy-eq-hom-inverse-sequential-diagram f)

  extensionality-hom-inverse-sequential-diagram :
    (f g : hom-inverse-sequential-diagram A B) →
    (f ＝ g) ≃ htpy-hom-inverse-sequential-diagram f g
  pr1 (extensionality-hom-inverse-sequential-diagram f g) =
    htpy-eq-hom-inverse-sequential-diagram f g
  pr2 (extensionality-hom-inverse-sequential-diagram f g) =
    is-equiv-htpy-eq-hom-inverse-sequential-diagram f g

  eq-htpy-hom-inverse-sequential-diagram :
    (f g : hom-inverse-sequential-diagram A B) →
    htpy-hom-inverse-sequential-diagram f g → f ＝ g
  eq-htpy-hom-inverse-sequential-diagram f g =
    map-inv-equiv (extensionality-hom-inverse-sequential-diagram f g)
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
