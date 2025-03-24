# Dependent universal property of suspensions

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.dependent-universal-property-suspensions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.constant-maps funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.homotopies funext
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-cocones-under-spans funext univalence truncations
open import synthetic-homotopy-theory.dependent-suspension-structures funext univalence truncations
open import synthetic-homotopy-theory.suspension-structures funext univalence truncations
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
