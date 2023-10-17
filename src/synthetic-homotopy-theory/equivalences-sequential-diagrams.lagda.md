# Equivalences of sequential diagrams

```agda
module synthetic-homotopy-theory.equivalences-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Definitions

### Equivalences of sequential diagrams

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  equiv-sequential-diagram : UU (l1 ⊔ l2)
  equiv-sequential-diagram =
    Σ ( ( n : ℕ) →
        family-sequential-diagram A n ≃ family-sequential-diagram B n)
      ( λ e → naturality-hom-sequential-diagram A B (map-equiv ∘ e))
```

### Components of equivalences of sequential diagrams

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( e : equiv-sequential-diagram A B)
  where

  equiv-equiv-sequential-diagram :
    ( n : ℕ) →
    family-sequential-diagram A n ≃ family-sequential-diagram B n
  equiv-equiv-sequential-diagram = pr1 e

  hom-equiv-sequential-diagram : hom-sequential-diagram A B
  pr1 hom-equiv-sequential-diagram n =
    map-equiv (equiv-equiv-sequential-diagram n)
  pr2 hom-equiv-sequential-diagram = pr2 e

  map-equiv-sequential-diagram :
    ( n : ℕ) →
    family-sequential-diagram A n → family-sequential-diagram B n
  map-equiv-sequential-diagram n = map-equiv (equiv-equiv-sequential-diagram n)

  is-equiv-map-equiv-sequential-diagram :
    ( n : ℕ) →
    is-equiv (map-equiv-sequential-diagram n)
  is-equiv-map-equiv-sequential-diagram n =
    is-equiv-map-equiv (equiv-equiv-sequential-diagram n)
```

### The identity equivalence of sequential diagrams

```agda
module _
  { l1 : Level} (A : sequential-diagram l1)
  where

  id-equiv-sequential-diagram : equiv-sequential-diagram A A
  pr1 id-equiv-sequential-diagram n = id-equiv
  pr2 id-equiv-sequential-diagram n = refl-htpy
```

### Composition of equivalences of sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  ( C : sequential-diagram l3)
  where

  comp-equiv-sequential-diagram :
    equiv-sequential-diagram B C →
    equiv-sequential-diagram A B →
    equiv-sequential-diagram A C
  pr1 (comp-equiv-sequential-diagram e e') n =
    ( equiv-equiv-sequential-diagram C e n) ∘e
    ( equiv-equiv-sequential-diagram B e' n)
  pr2 (comp-equiv-sequential-diagram e e') =
    naturality-map-hom-sequential-diagram C
      ( comp-hom-sequential-diagram A B C
        ( hom-equiv-sequential-diagram C e)
        ( hom-equiv-sequential-diagram B e'))
```

## Properties

### Characterization of equality of sequential diagrams

```agda
equiv-eq-sequential-diagram :
  { l1 : Level} (A B : sequential-diagram l1) →
  A ＝ B → equiv-sequential-diagram A B
equiv-eq-sequential-diagram A .A refl = id-equiv-sequential-diagram A

abstract
  is-torsorial-equiv-sequential-diagram :
    { l1 : Level} (A : sequential-diagram l1) →
    is-contr (Σ (sequential-diagram l1) (equiv-sequential-diagram A))
  is-torsorial-equiv-sequential-diagram A =
    is-torsorial-Eq-structure _
      ( is-torsorial-Eq-Π
        ( λ n → family-sequential-diagram A n ≃_)
        ( λ n → is-torsorial-equiv (family-sequential-diagram A n)))
      ( family-sequential-diagram A , λ n → id-equiv)
      ( is-torsorial-Eq-Π
        ( λ n → _~ map-sequential-diagram A n)
        ( λ n → is-torsorial-htpy' (map-sequential-diagram A n)))

  is-equiv-equiv-eq-sequential-diagram :
    { l1 : Level} (A B : sequential-diagram l1) →
    is-equiv (equiv-eq-sequential-diagram A B)
  is-equiv-equiv-eq-sequential-diagram A =
    fundamental-theorem-id
      ( is-torsorial-equiv-sequential-diagram A)
      ( equiv-eq-sequential-diagram A)

extensionality-sequential-diagram :
  { l1 : Level} (A B : sequential-diagram l1) →
  ( A ＝ B) ≃ equiv-sequential-diagram A B
pr1 (extensionality-sequential-diagram A B) = equiv-eq-sequential-diagram A B
pr2 (extensionality-sequential-diagram A B) =
  is-equiv-equiv-eq-sequential-diagram A B

eq-equiv-sequential-diagram :
  { l1 : Level} (A B : sequential-diagram l1) →
  equiv-sequential-diagram A B → (A ＝ B)
eq-equiv-sequential-diagram A B =
  map-inv-equiv (extensionality-sequential-diagram A B)
```
