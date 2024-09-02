# Isometries between metric spaces

```agda
module metric-spaces.isometry-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.sets
open import foundation.subtypes
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometry-premetric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) is an
{{#concept "isometry" Disambiguation="between metric spaces" Agda=is-isometry-Metric-Space}}
if it transports [premetrics](metric-spaces.premetric-structures.md).

## Definitions

### The property of being a isometry between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : function-carrier-type-Metric-Space A B)
  where

  is-isometry-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-isometry-prop-Metric-Space =
    is-isometry-prop-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
      ( f)

  is-isometry-Metric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-isometry-Metric-Space =
    type-Prop is-isometry-prop-Metric-Space

  is-prop-is-isometry-Metric-Space :
    is-prop is-isometry-Metric-Space
  is-prop-is-isometry-Metric-Space =
    is-prop-type-Prop is-isometry-prop-Metric-Space
```

### The set of isometries between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  set-isometry-Metric-Space : Set (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  set-isometry-Metric-Space =
    set-subset
      ( set-function-carrier-type-Metric-Space A B)
      ( is-isometry-prop-Metric-Space A B)

  isometry-Metric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometry-Metric-Space = type-Set set-isometry-Metric-Space

  is-set-isometry-Metric-Space : is-set isometry-Metric-Space
  is-set-isometry-Metric-Space =
    is-set-type-Set set-isometry-Metric-Space

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : isometry-Metric-Space A B)
  where

  map-isometry-Metric-Space : function-carrier-type-Metric-Space A B
  map-isometry-Metric-Space =
    map-isometry-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
      ( f)

  is-isometry-map-isometry-Metric-Space :
    is-isometry-Metric-Space A B map-isometry-Metric-Space
  is-isometry-map-isometry-Metric-Space =
    is-isometry-map-isometry-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
      ( f)
```

## Properties

### The identity function on a metric space is an isometry

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-isometry-id-Metric-Space :
    is-isometry-Metric-Space A A (id-Metric-Space A)
  is-isometry-id-Metric-Space d x y = id-iff

  isometry-id-Metric-Space : isometry-Metric-Space A A
  isometry-id-Metric-Space =
    id-Metric-Space A , is-isometry-id-Metric-Space
```

### Equality of isometries in metric spaces is equivalent to homotopies between their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f g : isometry-Metric-Space A B)
  where

  equiv-eq-htpy-map-isometry-Metric-Space :
    (f ＝ g) ≃
    (map-isometry-Metric-Space A B f ~ map-isometry-Metric-Space A B g)
  equiv-eq-htpy-map-isometry-Metric-Space =
    equiv-eq-htpy-map-isometry-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
      ( f)
      ( g)

  htpy-eq-map-isometry-Metric-Space :
    (f ＝ g) →
    (map-isometry-Metric-Space A B f ~ map-isometry-Metric-Space A B g)
  htpy-eq-map-isometry-Metric-Space =
    map-equiv equiv-eq-htpy-map-isometry-Metric-Space

  eq-htpy-map-isometry-Metric-Space :
    (map-isometry-Metric-Space A B f ~ map-isometry-Metric-Space A B g) →
    (f ＝ g)
  eq-htpy-map-isometry-Metric-Space =
    map-inv-equiv equiv-eq-htpy-map-isometry-Metric-Space
```

### Composition of isometries

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  (g : isometry-Metric-Space B C)
  (f : isometry-Metric-Space A B)
  where

  comp-isometry-Metric-Space :
    isometry-Metric-Space A C
  comp-isometry-Metric-Space =
    ( map-isometry-Metric-Space B C g ∘
      map-isometry-Metric-Space A B f) ,
    ( preserves-isometry-comp-function-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
      ( premetric-Metric-Space C)
      ( map-isometry-Metric-Space B C g)
      ( map-isometry-Metric-Space A B f)
      ( is-isometry-map-isometry-Metric-Space B C g)
      ( is-isometry-map-isometry-Metric-Space A B f))
```

### The isometric inverse of an isometric equivalence

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : function-carrier-type-Metric-Space A B)
  (E : is-equiv f)
  (I : is-isometry-Metric-Space A B f)
  where

  isometry-inv-is-equiv-is-isometry-Metric-Space :
    isometry-Metric-Space B A
  isometry-inv-is-equiv-is-isometry-Metric-Space =
    ( map-inv-is-equiv E) ,
    ( is-isometry-map-inv-is-equiv-is-isometry-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
      ( f)
      ( E)
      ( I))
```
