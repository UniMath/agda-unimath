# Dependent universal property of suspensions

```agda
module synthetic-homotopy-theory.dependent-universal-property-suspensions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-suspension-structures
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.universal-property-suspensions
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
  (susp-str : suspension-structure X Y) (B : Y → UU l3) →
  ((y : Y) → B y) →
  dependent-suspension-structure B susp-str
pr1 (dependent-ev-suspension susp-str B s) =
  s (north-suspension-structure susp-str)
pr1 (pr2 (dependent-ev-suspension susp-str B s)) =
  s (south-suspension-structure susp-str)
pr2 (pr2 (dependent-ev-suspension susp-str B s)) =
  (apd s) ∘ (meridian-suspension-structure susp-str)

module _
  (l : Level) {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (susp-str : suspension-structure X Y)
  where

  dependent-universal-property-suspension : UU (l1 ⊔ l2 ⊔ lsuc l)
  dependent-universal-property-suspension =
    (B : Y → UU l) → is-equiv (dependent-ev-suspension susp-str B)
```

#### Coherence between `dependent-ev-suspension` and

`dependent-cocone-map`

```agda
triangle-dependent-ev-suspension :
    {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
    (susp-str : suspension-structure X Y) →
    (B : Y → UU l3) →
  ( ( map-equiv
    ( equiv-dependent-suspension-structure-suspension-cocone susp-str B)) ∘
  ( dependent-cocone-map
    ( const X unit star)
    ( const X unit star)
    ( cocone-suspension-structure X Y susp-str)
    ( B))) ~
  ( dependent-ev-suspension susp-str B)
triangle-dependent-ev-suspension {X = X} {Y = Y} susp-str B = refl-htpy
```
