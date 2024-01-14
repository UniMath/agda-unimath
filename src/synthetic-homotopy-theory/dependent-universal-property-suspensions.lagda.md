# Dependent universal property of suspensions

```agda
module synthetic-homotopy-theory.dependent-universal-property-suspensions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-suspension-structures
open import synthetic-homotopy-theory.suspension-structures
```

</details>

## Idea

This is the dependent analog of the
[universal property of suspensions](synthetic-homotopy-theory.universal-property-suspensions.md).

## Definition

### The dependent universal property of suspensions

```agda
dependent-ev-suspension :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  (s : suspension-structure X Y) (B : Y → UU l3) →
  ((y : Y) → B y) →
  dependent-suspension-structure B s
pr1 (dependent-ev-suspension s B f) =
  f (north-suspension-structure s)
pr1 (pr2 (dependent-ev-suspension s B f)) =
  f (south-suspension-structure s)
pr2 (pr2 (dependent-ev-suspension s B f)) =
  apd f ∘ meridian-suspension-structure s

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (s : suspension-structure X Y)
  where

  dependent-universal-property-suspension : UUω
  dependent-universal-property-suspension =
    {l : Level} (B : Y → UU l) → is-equiv (dependent-ev-suspension s B)
```

#### Coherence between `dependent-ev-suspension` and `dependent-cocone-map`

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  where

  triangle-dependent-ev-suspension :
    (s : suspension-structure X Y) →
    (B : Y → UU l3) →
    ( ( map-equiv
        ( equiv-dependent-suspension-structure-suspension-cocone s B)) ∘
      ( dependent-cocone-map
        ( terminal-map X)
        ( terminal-map X)
        ( suspension-cocone-suspension-structure s)
        ( B))) ~
    ( dependent-ev-suspension s B)
  triangle-dependent-ev-suspension s B = refl-htpy
```
