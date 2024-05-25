# Equivalences of inverse sequential diagrams of types

```agda
module foundation.equivalences-inverse-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.inverse-sequential-diagrams
open import foundation.morphisms-inverse-sequential-diagrams
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

An
{{#concept "equivalence of inverse sequential diagrams" Agda=equiv-inverse-sequential-diagram}}
`A ≃ B` is a commuting diagram of the form

```text
  ⋯ ----> Aₙ₊₁ ----> Aₙ ----> ⋯ ----> A₁ ----> A₀
           |         |       |       |        |
  ⋯        |         |       ⋯       |        |
           ∨         ∨       ∨       ∨        ∨
  ⋯ ----> Bₙ₊₁ ----> Bₙ ----> ⋯ ----> B₁ ----> B₀.
```

where every vertical map is an [equivalence](foundation-core.equivalences.md).

## Definitions

```agda
equiv-inverse-sequential-diagram :
  {l1 l2 : Level}
  (A : inverse-sequential-diagram l1)
  (B : inverse-sequential-diagram l2) →
  UU (l1 ⊔ l2)
equiv-inverse-sequential-diagram A B =
  Σ ( (n : ℕ) →
      family-inverse-sequential-diagram A n ≃
      family-inverse-sequential-diagram B n)
    ( λ e →
      (n : ℕ) → naturality-hom-inverse-sequential-diagram A B (map-equiv ∘ e) n)

hom-equiv-inverse-sequential-diagram :
  {l1 l2 : Level}
  (A : inverse-sequential-diagram l1)
  (B : inverse-sequential-diagram l2) →
  equiv-inverse-sequential-diagram A B →
  hom-inverse-sequential-diagram A B
pr1 (hom-equiv-inverse-sequential-diagram A B e) n = pr1 (pr1 e n)
pr2 (hom-equiv-inverse-sequential-diagram A B e) = pr2 e
```

## Properties

### Characterizing equality of inverse sequential diagrams

```agda
id-equiv-inverse-sequential-diagram :
  {l : Level} (A : inverse-sequential-diagram l) →
  equiv-inverse-sequential-diagram A A
pr1 (id-equiv-inverse-sequential-diagram A) n = id-equiv
pr2 (id-equiv-inverse-sequential-diagram A) n = refl-htpy

equiv-eq-inverse-sequential-diagram :
  {l : Level} (A B : inverse-sequential-diagram l) →
  A ＝ B → equiv-inverse-sequential-diagram A B
equiv-eq-inverse-sequential-diagram A .A refl =
  id-equiv-inverse-sequential-diagram A

is-torsorial-equiv-inverse-sequential-diagram :
  {l : Level} (A : inverse-sequential-diagram l) →
  is-torsorial (equiv-inverse-sequential-diagram A)
is-torsorial-equiv-inverse-sequential-diagram A =
  is-torsorial-Eq-structure
    ( is-torsorial-Eq-Π
      ( λ n → is-torsorial-equiv (family-inverse-sequential-diagram A n)))
    ( family-inverse-sequential-diagram A , λ n → id-equiv)
    ( is-torsorial-Eq-Π
      ( λ n → is-torsorial-htpy (map-inverse-sequential-diagram A n)))

is-equiv-equiv-eq-inverse-sequential-diagram :
  {l : Level} (A B : inverse-sequential-diagram l) →
  is-equiv (equiv-eq-inverse-sequential-diagram A B)
is-equiv-equiv-eq-inverse-sequential-diagram A =
  fundamental-theorem-id
    ( is-torsorial-equiv-inverse-sequential-diagram A)
    ( equiv-eq-inverse-sequential-diagram A)

eq-equiv-inverse-sequential-diagram :
  {l : Level} {A B : inverse-sequential-diagram l} →
  equiv-inverse-sequential-diagram A B → A ＝ B
eq-equiv-inverse-sequential-diagram {A = A} {B} =
  map-inv-is-equiv (is-equiv-equiv-eq-inverse-sequential-diagram A B)
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
