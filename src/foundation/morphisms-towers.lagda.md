# Morphisms of towers of types

```agda
module foundation.morphisms-towers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.dependent-towers
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.towers
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A **morphism of towers** `A → B` is a commuting diagram of the form

```text
  ⋯ ----> Aₙ₊₁ ----> Aₙ ----> ⋯ ----> A₁ ----> A₀
           |         |       |       |        |
  ⋯        |         |       ⋯       |        |
           v         v       v       v        v
  ⋯ ----> Bₙ₊₁ ----> Bₙ ----> ⋯ ----> B₁ ----> B₀.
```

## Definitions

### Morphisms of towers

```agda
naturality-hom-tower :
  {l1 l2 : Level} (A : tower l1) (B : tower l2)
  (h : (n : ℕ) → type-tower A n → type-tower B n) (n : ℕ) → UU (l1 ⊔ l2)
naturality-hom-tower A B =
  naturality-section-dependent-tower A (const-dependent-tower A B)

hom-tower : {l1 l2 : Level} (A : tower l1) (B : tower l2) → UU (l1 ⊔ l2)
hom-tower A B = section-dependent-tower A (const-dependent-tower A B)

module _
  {l1 l2 : Level} (A : tower l1) (B : tower l2)
  where

  map-hom-tower : hom-tower A B → (n : ℕ) → type-tower A n → type-tower B n
  map-hom-tower = map-section-dependent-tower A (const-dependent-tower A B)

  naturality-map-hom-tower :
    (f : hom-tower A B) (n : ℕ) → naturality-hom-tower A B (map-hom-tower f) n
  naturality-map-hom-tower =
    naturality-map-section-dependent-tower A (const-dependent-tower A B)
```

### Identity map on towers

```agda
id-hom-tower :
  {l : Level} (A : tower l) → hom-tower A A
pr1 (id-hom-tower A) n = id
pr2 (id-hom-tower A) n = refl-htpy
```

### Composition of map of towers

```agda
map-comp-hom-tower :
  {l : Level} (A B C : tower l) → hom-tower B C → hom-tower A B →
  (n : ℕ) → type-tower A n → type-tower C n
map-comp-hom-tower A B C g f n = map-hom-tower B C g n ∘ map-hom-tower A B f n

naturality-comp-hom-tower :
  {l : Level} (A B C : tower l) (g : hom-tower B C) (f : hom-tower A B)
  (n : ℕ) → naturality-hom-tower A C (map-comp-hom-tower A B C g f) n
naturality-comp-hom-tower A B C g f n x =
  ( ap (map-hom-tower B C g n) (naturality-map-hom-tower A B f n x)) ∙
  ( naturality-map-hom-tower B C g n (map-hom-tower A B f (succ-ℕ n) x))

comp-hom-tower :
  {l : Level} (A B C : tower l) → hom-tower B C → hom-tower A B → hom-tower A C
pr1 (comp-hom-tower A B C g f) = map-comp-hom-tower A B C g f
pr2 (comp-hom-tower A B C g f) = naturality-comp-hom-tower A B C g f
```

## Properties

### Characterization of equality of maps of towers

```agda
module _
  {l1 l2 : Level} (A : tower l1) (B : tower l2)
  where

  coherence-htpy-hom-tower :
    (f g : hom-tower A B) →
    ((n : ℕ) → map-hom-tower A B f n ~ map-hom-tower A B g n) →
    (n : ℕ) → UU (l1 ⊔ l2)
  coherence-htpy-hom-tower f g H n =
    ( naturality-map-hom-tower A B f n ∙h (map-tower B n ·l H (succ-ℕ n))) ~
    ( (H n ·r map-tower A n) ∙h naturality-map-hom-tower A B g n)

  htpy-hom-tower :
    (f g : hom-tower A B) → UU (l1 ⊔ l2)
  htpy-hom-tower f g =
    Σ ( (n : ℕ) → map-hom-tower A B f n ~ map-hom-tower A B g n)
      ( λ H → (n : ℕ) → coherence-htpy-hom-tower f g H n)

  refl-htpy-hom-tower : (f : hom-tower A B) → htpy-hom-tower f f
  pr1 (refl-htpy-hom-tower f) n = refl-htpy
  pr2 (refl-htpy-hom-tower f) n = right-unit-htpy

  htpy-eq-hom-tower : (f g : hom-tower A B) → f ＝ g → htpy-hom-tower f g
  htpy-eq-hom-tower f .f refl = refl-htpy-hom-tower f

  is-torsorial-htpy-hom-tower :
    (f : hom-tower A B) → is-torsorial (htpy-hom-tower f)
  is-torsorial-htpy-hom-tower f =
    is-torsorial-Eq-structure _
      ( is-torsorial-binary-htpy (map-hom-tower A B f))
      ( map-hom-tower A B f , refl-binary-htpy (map-hom-tower A B f))
      ( is-torsorial-Eq-Π _
        ( λ n →
          is-torsorial-htpy (naturality-map-hom-tower A B f n ∙h refl-htpy)))

  is-equiv-htpy-eq-hom-tower :
    (f g : hom-tower A B) → is-equiv (htpy-eq-hom-tower f g)
  is-equiv-htpy-eq-hom-tower f =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-tower f)
      ( htpy-eq-hom-tower f)

  extensionality-hom-tower :
    (f g : hom-tower A B) → (f ＝ g) ≃ htpy-hom-tower f g
  pr1 (extensionality-hom-tower f g) = htpy-eq-hom-tower f g
  pr2 (extensionality-hom-tower f g) = is-equiv-htpy-eq-hom-tower f g

  eq-htpy-hom-tower : (f g : hom-tower A B) → htpy-hom-tower f g → f ＝ g
  eq-htpy-hom-tower f g = map-inv-equiv (extensionality-hom-tower f g)
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
