# Equivalences of towers of types

```agda
module foundation.equivalences-towers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.morphisms-towers
open import foundation.structure-identity-principle
open import foundation.towers
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

An **equivalence of towers** `A ≃ B` is a commuting diagram of the form

```text
  ⋯ ----> Aₙ₊₁ ----> Aₙ ----> ⋯ ----> A₁ ----> A₀
           |         |       |       |        |
  ⋯        |         |       ⋯       |        |
           v         v       v       v        v
  ⋯ ----> Bₙ₊₁ ----> Bₙ ----> ⋯ ----> B₁ ----> B₀.
```

where every vertical map is an [equivalence](foundation-core.equivalences.md).

## Definitions

```agda
equiv-tower :
  {l1 l2 : Level} (A : tower l1) (B : tower l2) → UU (l1 ⊔ l2)
equiv-tower A B =
  Σ ( (n : ℕ) → type-tower A n ≃ type-tower B n)
    ( λ e → (n : ℕ) → naturality-hom-tower A B (map-equiv ∘ e) n)

hom-equiv-tower :
  {l1 l2 : Level} (A : tower l1) (B : tower l2) →
  equiv-tower A B → hom-tower A B
pr1 (hom-equiv-tower A B e) n = pr1 (pr1 e n)
pr2 (hom-equiv-tower A B e) = pr2 e
```

## Properties

### Characterizing equality of towers

```agda
id-equiv-tower :
  {l : Level} (A : tower l) → equiv-tower A A
pr1 (id-equiv-tower A) n = id-equiv
pr2 (id-equiv-tower A) n = refl-htpy

equiv-eq-tower :
  {l : Level} (A B : tower l) → A ＝ B → equiv-tower A B
equiv-eq-tower A .A refl = id-equiv-tower A

is-torsorial-equiv-tower :
  {l : Level} (A : tower l) → is-torsorial (equiv-tower A)
is-torsorial-equiv-tower A =
  is-torsorial-Eq-structure _
    ( is-torsorial-Eq-Π
      ( λ n → type-tower A n ≃_)
      ( λ n → is-torsorial-equiv (type-tower A n)))
    ( type-tower A , λ n → id-equiv)
    ( is-torsorial-Eq-Π _
      ( λ n → is-torsorial-htpy (map-tower A n)))

is-equiv-equiv-eq-tower :
  {l : Level} (A B : tower l) → is-equiv (equiv-eq-tower A B)
is-equiv-equiv-eq-tower A =
  fundamental-theorem-id
    ( is-torsorial-equiv-tower A)
    ( equiv-eq-tower A)

eq-equiv-tower :
  {l : Level} {A B : tower l} → equiv-tower A B → A ＝ B
eq-equiv-tower {A = A} {B} = map-inv-is-equiv (is-equiv-equiv-eq-tower A B)
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
