# Expansive maps between metric spaces

```agda
module metric-spaces.expansive-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.expansive-maps-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.poset-of-rational-neighborhood-relations
open import metric-spaces.preimages-rational-neighborhood-relations
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

A [map](metric-spaces.maps-metric-spaces.md) `f` between two
[metric spaces](metric-spaces.metric-spaces.md) `A` and `B` is
{{#concept "expansive" Disambiguation="maps between metric spaces" Agda=is-expansive-map-Metric-Space}}
if for any two points `x` and `y` in `A`, if `f x` and `f y` share an
`ε`-neighborhood in `B` then `x` and `y` share an `ε`-neighborhood in `A`. In
other words, `f` reflects neighborhoods.

## Definitions

### The property of being an expansive map between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : map-Metric-Space A B)
  where

  is-expansive-map-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-expansive-map-prop-Metric-Space =
    is-expansive-map-prop-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

  is-expansive-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-expansive-map-Metric-Space =
    type-Prop is-expansive-map-prop-Metric-Space

  is-prop-is-expansive-map-Metric-Space :
    is-prop is-expansive-map-Metric-Space
  is-prop-is-expansive-map-Metric-Space =
    is-prop-type-Prop is-expansive-map-prop-Metric-Space
```

### The set of expansive maps between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  expansive-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  expansive-map-Metric-Space =
    expansive-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)

  expansive-map-set-Metric-Space : Set (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  expansive-map-set-Metric-Space =
    set-subset
      ( map-set-Metric-Space A B)
      ( is-expansive-map-prop-Metric-Space A B)

  abstract
    is-set-expansive-map-Metric-Space :
      is-set expansive-map-Metric-Space
    is-set-expansive-map-Metric-Space =
      is-set-type-Set expansive-map-set-Metric-Space

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : expansive-map-Metric-Space A B)
  where

  map-expansive-map-Metric-Space : map-Metric-Space A B
  map-expansive-map-Metric-Space =
    map-expansive-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

  is-expansive-map-expansive-map-Metric-Space :
    is-expansive-map-Metric-Space A B map-expansive-map-Metric-Space
  is-expansive-map-expansive-map-Metric-Space =
    is-expansive-map-expansive-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
```

## Properties

### The identity map on a metric space is expansive

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-expansive-map-id-map-Metric-Space :
    is-expansive-map-Metric-Space A A (id-map-Metric-Space A)
  is-expansive-map-id-map-Metric-Space =
    is-expansive-map-id-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)

  id-expansive-map-Metric-Space : expansive-map-Metric-Space A A
  id-expansive-map-Metric-Space =
    id-expansive-map-Pseudometric-Space (pseudometric-Metric-Space A)
```

### Equality of expansive maps between metric spaces is characterized by homotopy of their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f g : expansive-map-Metric-Space A B)
  where

  htpy-map-expansive-map-Metric-Space : UU (l1 ⊔ l1')
  htpy-map-expansive-map-Metric-Space =
    map-expansive-map-Metric-Space A B f ~ map-expansive-map-Metric-Space A B g

  equiv-eq-htpy-map-expansive-map-Metric-Space :
    (f ＝ g) ≃ htpy-map-expansive-map-Metric-Space
  equiv-eq-htpy-map-expansive-map-Metric-Space =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-expansive-map-prop-Metric-Space A B) f g

  eq-htpy-map-expansive-map-Metric-Space :
    htpy-map-expansive-map-Metric-Space → f ＝ g
  eq-htpy-map-expansive-map-Metric-Space =
    map-inv-equiv equiv-eq-htpy-map-expansive-map-Metric-Space
```

### Composition of expansive maps

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  where

  is-expansive-map-comp-Metric-Space :
    (g : map-Metric-Space B C) →
    (f : map-Metric-Space A B) →
    is-expansive-map-Metric-Space B C g →
    is-expansive-map-Metric-Space A B f →
    is-expansive-map-Metric-Space A C (g ∘ f)
  is-expansive-map-comp-Metric-Space =
    is-expansive-map-comp-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( pseudometric-Metric-Space C)

  comp-expansive-map-Metric-Space :
    expansive-map-Metric-Space B C →
    expansive-map-Metric-Space A B →
    expansive-map-Metric-Space A C
  comp-expansive-map-Metric-Space =
    comp-expansive-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( pseudometric-Metric-Space C)
```

### Unit laws for composition of expansive maps between metric spaces

```agda
module _
  {l1a l2a l1b l2b : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (f : expansive-map-Metric-Space A B)
  where

  left-unit-law-comp-expansive-map-Metric-Space :
    ( comp-expansive-map-Metric-Space A B B
      ( id-expansive-map-Metric-Space B)
      ( f)) ＝
    ( f)
  left-unit-law-comp-expansive-map-Metric-Space =
    left-unit-law-comp-expansive-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

  right-unit-law-comp-expansive-map-Metric-Space :
    ( comp-expansive-map-Metric-Space A A B
      ( f)
      ( id-expansive-map-Metric-Space A)) ＝
    ( f)
  right-unit-law-comp-expansive-map-Metric-Space =
    right-unit-law-comp-expansive-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
```

### Associativity of composition of expansive maps between metric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c l1d l2d : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  (D : Metric-Space l1d l2d)
  (h : expansive-map-Metric-Space C D)
  (g : expansive-map-Metric-Space B C)
  (f : expansive-map-Metric-Space A B)
  where

  associative-comp-expansive-map-Metric-Space :
    ( comp-expansive-map-Metric-Space A B D
      ( comp-expansive-map-Metric-Space B C D h g)
        ( f)) ＝
    ( comp-expansive-map-Metric-Space A C D
      ( h)
      ( comp-expansive-map-Metric-Space A B C g f))
  associative-comp-expansive-map-Metric-Space =
    associative-comp-expansive-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( pseudometric-Metric-Space C)
      ( pseudometric-Metric-Space D)
      ( h)
      ( g)
      ( f)
```

### Any isometry between metric spaces is expansive

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : map-Metric-Space A B)
  where

  is-expansive-map-is-isometry-Metric-Space :
    is-isometry-Metric-Space A B f →
    is-expansive-map-Metric-Space A B f
  is-expansive-map-is-isometry-Metric-Space =
    is-expansive-map-is-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
```

### The embedding of isometries of metric spaces into expansive maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  expansive-map-isometry-Metric-Space :
    isometry-Metric-Space A B → expansive-map-Metric-Space A B
  expansive-map-isometry-Metric-Space =
    expansive-map-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)

  is-emb-expansive-map-isometry-Metric-Space :
    is-emb expansive-map-isometry-Metric-Space
  is-emb-expansive-map-isometry-Metric-Space =
    is-emb-expansive-map-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)

  emb-expansive-map-isometry-Metric-Space :
    isometry-Metric-Space A B ↪ expansive-map-Metric-Space A B
  emb-expansive-map-isometry-Metric-Space =
    emb-expansive-map-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
```

### The action on sequences of expansive maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : expansive-map-Metric-Space X Y)
  where

  map-sequence-expansive-map-Metric-Space :
    sequence-type-Metric-Space X → sequence-type-Metric-Space Y
  map-sequence-expansive-map-Metric-Space =
    map-sequence (map-expansive-map-Metric-Space X Y f)
```
