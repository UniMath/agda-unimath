# Retracts of sequential diagrams

```agda
module synthetic-homotopy-theory.retracts-of-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

A
{{#concept "retract" Disambiguation="sequential diagram" Agda=retract-sequential-diagram}}
of sequential diagrams `A` of `B` is a
[morphism of sequential diagrams](synthetic-homotopy-theory.morphisms-sequential-diagrams.md)
`B → A` that is a retraction.

## Definitions

### The predicate of being a retraction of sequential diagrams

```agda
module _
  {l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  (i : hom-sequential-diagram A B) (r : hom-sequential-diagram B A)
  where

  is-retraction-hom-sequential-diagram : UU l1
  is-retraction-hom-sequential-diagram =
    htpy-hom-sequential-diagram A
      ( comp-hom-sequential-diagram A B A r i)
      ( id-hom-sequential-diagram A)
```

### The type of retractions of a morphism of sequential diagrams

```agda
module _
  {l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  (i : hom-sequential-diagram A B)
  where

  retraction-hom-sequential-diagram : UU (l1 ⊔ l2)
  retraction-hom-sequential-diagram =
    Σ (hom-sequential-diagram B A) (is-retraction-hom-sequential-diagram A B i)

  module _
    (r : retraction-hom-sequential-diagram)
    where

    hom-retraction-hom-sequential-diagram : hom-sequential-diagram B A
    hom-retraction-hom-sequential-diagram = pr1 r

    is-retraction-hom-retraction-hom-sequential-diagram :
      is-retraction-hom-sequential-diagram A B i
        ( hom-retraction-hom-sequential-diagram)
    is-retraction-hom-retraction-hom-sequential-diagram = pr2 r
```

### The predicate that a sequential diagram `A` is a retract of a sequential diagram `B`

```agda
retract-sequential-diagram :
  {l1 l2 : Level} (B : sequential-diagram l2) (A : sequential-diagram l1) →
  UU (l1 ⊔ l2)
retract-sequential-diagram B A =
  Σ (hom-sequential-diagram A B) (retraction-hom-sequential-diagram A B)
```

### The higher coherence in the definition of retracts of sequential diagrams

```agda
module _
  {l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  (i : hom-sequential-diagram A B) (r : hom-sequential-diagram B A)
  where

  coherence-retract-sequential-diagram :
    ( (n : ℕ) →
      is-retraction
        ( map-hom-sequential-diagram B i n)
        ( map-hom-sequential-diagram A r n)) →
    UU l1
  coherence-retract-sequential-diagram =
    coherence-htpy-hom-sequential-diagram A
      ( comp-hom-sequential-diagram A B A r i)
      ( id-hom-sequential-diagram A)
```

### The binary relation `A B ↦ A retract-of-sequential-diagram B` asserting that `A` is a retract of the sequential diagram `B`

```agda
module _
  {l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  infix 6 _retract-of-sequential-diagram_

  _retract-of-sequential-diagram_ : UU (l1 ⊔ l2)
  _retract-of-sequential-diagram_ = retract-sequential-diagram B A

module _
  {l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  (R : A retract-of-sequential-diagram B)
  where

  inclusion-retract-sequential-diagram : hom-sequential-diagram A B
  inclusion-retract-sequential-diagram = pr1 R

  map-inclusion-retract-sequential-diagram :
    (n : ℕ) → family-sequential-diagram A n → family-sequential-diagram B n
  map-inclusion-retract-sequential-diagram =
    map-hom-sequential-diagram B inclusion-retract-sequential-diagram

  naturality-inclusion-retract-sequential-diagram :
    naturality-hom-sequential-diagram A B
      ( map-inclusion-retract-sequential-diagram)
  naturality-inclusion-retract-sequential-diagram =
    naturality-map-hom-sequential-diagram B
      ( inclusion-retract-sequential-diagram)

  retraction-retract-sequential-diagram :
    retraction-hom-sequential-diagram A B inclusion-retract-sequential-diagram
  retraction-retract-sequential-diagram = pr2 R

  hom-retraction-retract-sequential-diagram : hom-sequential-diagram B A
  hom-retraction-retract-sequential-diagram =
    hom-retraction-hom-sequential-diagram A B
      ( inclusion-retract-sequential-diagram)
      ( retraction-retract-sequential-diagram)

  map-hom-retraction-retract-sequential-diagram :
    (n : ℕ) → family-sequential-diagram B n → family-sequential-diagram A n
  map-hom-retraction-retract-sequential-diagram =
    map-hom-sequential-diagram A hom-retraction-retract-sequential-diagram

  naturality-hom-retraction-retract-sequential-diagram :
    naturality-hom-sequential-diagram B A
      ( map-hom-retraction-retract-sequential-diagram)
  naturality-hom-retraction-retract-sequential-diagram =
    naturality-map-hom-sequential-diagram A
      ( hom-retraction-retract-sequential-diagram)

  is-retraction-hom-retraction-retract-sequential-diagram :
    is-retraction-hom-sequential-diagram A B
      ( inclusion-retract-sequential-diagram)
      ( hom-retraction-retract-sequential-diagram)
  is-retraction-hom-retraction-retract-sequential-diagram =
    is-retraction-hom-retraction-hom-sequential-diagram A B
      ( inclusion-retract-sequential-diagram)
      ( retraction-retract-sequential-diagram)

  is-retraction-map-hom-retraction-retract-sequential-diagram :
    (n : ℕ) →
    is-retraction
      ( map-inclusion-retract-sequential-diagram n)
      ( map-hom-retraction-retract-sequential-diagram n)
  is-retraction-map-hom-retraction-retract-sequential-diagram =
    htpy-htpy-hom-sequential-diagram A
      ( is-retraction-hom-retraction-retract-sequential-diagram)

  retract-family-retract-sequential-diagram :
    (n : ℕ) →
    ( family-sequential-diagram A n) retract-of
    ( family-sequential-diagram B n)
  pr1 (retract-family-retract-sequential-diagram n) =
    map-inclusion-retract-sequential-diagram n
  pr1 (pr2 (retract-family-retract-sequential-diagram n)) =
    map-hom-retraction-retract-sequential-diagram n
  pr2 (pr2 (retract-family-retract-sequential-diagram n)) =
    is-retraction-map-hom-retraction-retract-sequential-diagram n

  coh-retract-sequential-diagram :
    coherence-retract-sequential-diagram A B
      ( inclusion-retract-sequential-diagram)
      ( hom-retraction-retract-sequential-diagram)
      ( is-retraction-map-hom-retraction-retract-sequential-diagram)
  coh-retract-sequential-diagram =
    coherence-htpy-htpy-hom-sequential-diagram A
      ( is-retraction-hom-retraction-retract-sequential-diagram)
```

## See also

- [Retracts of arrows](foundation.retracts-of-arrows.md)
