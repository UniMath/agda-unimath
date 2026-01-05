# Short maps between metric spaces

```agda
module metric-spaces.short-maps-metric-spaces where
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

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.poset-of-rational-neighborhood-relations
open import metric-spaces.preimages-rational-neighborhood-relations
open import metric-spaces.short-maps-pseudometric-spaces
```

</details>

## Idea

A [map](metric-spaces.maps-metric-spaces.md) `f` between two
[metric spaces](metric-spaces.metric-spaces.md) `A` and `B` is
{{#concept "short" Disambiguation="maps between metric spaces" Agda=is-short-map-Metric-Space WD="metric map" WDID=Q2713824}}
if it's [short](metric-spaces.short-maps-pseudometric-spaces.md) between their
underlying [pseudometric spaces](metric-spaces.pseudometric-spaces.md). That is,
if the
[rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
on `A` is [finer](metric-spaces.poset-of-rational-neighborhood-relations.md)
than the [preimage](metric-spaces.preimages-rational-neighborhood-relations.md)
by `f` of the rational neighborhood relation on `B`. I.e., upper bounds on the
distance between two points in `A` are upper bounds of the distance between
their images in `B`.

## Definitions

### The property of being a short map between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : map-Metric-Space A B)
  where

  is-short-map-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-short-map-prop-Metric-Space =
    is-short-map-prop-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

  is-short-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-short-map-Metric-Space =
    type-Prop is-short-map-prop-Metric-Space

  is-prop-is-short-map-Metric-Space :
    is-prop is-short-map-Metric-Space
  is-prop-is-short-map-Metric-Space =
    is-prop-type-Prop is-short-map-prop-Metric-Space
```

### The set of short maps between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  short-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  short-map-Metric-Space =
    short-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)

  short-map-set-Metric-Space : Set (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  short-map-set-Metric-Space =
    set-subset
      ( map-set-Metric-Space A B)
      ( is-short-map-prop-Metric-Space A B)

  abstract
    is-set-short-map-Metric-Space :
      is-set short-map-Metric-Space
    is-set-short-map-Metric-Space =
      is-set-type-Set short-map-set-Metric-Space

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-map-Metric-Space A B)
  where

  map-short-map-Metric-Space : map-Metric-Space A B
  map-short-map-Metric-Space =
    map-short-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

  is-short-map-short-map-Metric-Space :
    is-short-map-Metric-Space A B map-short-map-Metric-Space
  is-short-map-short-map-Metric-Space =
    is-short-map-short-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
```

## Properties

### The identity map on a metric space is short

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-short-map-id-map-Metric-Space :
    is-short-map-Metric-Space A A (id-map-Metric-Space A)
  is-short-map-id-map-Metric-Space =
    is-short-map-id-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)

  id-short-map-Metric-Space : short-map-Metric-Space A A
  id-short-map-Metric-Space =
    id-short-map-Pseudometric-Space (pseudometric-Metric-Space A)
```

### Equality of short maps between metric spaces is characterized by homotopy of their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f g : short-map-Metric-Space A B)
  where

  htpy-map-short-map-Metric-Space : UU (l1 ⊔ l1')
  htpy-map-short-map-Metric-Space =
    map-short-map-Metric-Space A B f ~ map-short-map-Metric-Space A B g

  equiv-eq-htpy-map-short-map-Metric-Space :
    (f ＝ g) ≃ htpy-map-short-map-Metric-Space
  equiv-eq-htpy-map-short-map-Metric-Space =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-short-map-prop-Metric-Space A B) f g

  eq-htpy-map-short-map-Metric-Space : htpy-map-short-map-Metric-Space → f ＝ g
  eq-htpy-map-short-map-Metric-Space =
    map-inv-equiv equiv-eq-htpy-map-short-map-Metric-Space
```

### Composition of short maps

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  where

  is-short-map-comp-Metric-Space :
    (g : map-Metric-Space B C) →
    (f : map-Metric-Space A B) →
    is-short-map-Metric-Space B C g →
    is-short-map-Metric-Space A B f →
    is-short-map-Metric-Space A C (g ∘ f)
  is-short-map-comp-Metric-Space =
    is-short-map-comp-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( pseudometric-Metric-Space C)

  comp-short-map-Metric-Space :
    short-map-Metric-Space B C →
    short-map-Metric-Space A B →
    short-map-Metric-Space A C
  comp-short-map-Metric-Space =
    comp-short-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( pseudometric-Metric-Space C)
```

### Unit laws for composition of short maps between metric spaces

```agda
module _
  {l1a l2a l1b l2b : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (f : short-map-Metric-Space A B)
  where

  left-unit-law-comp-short-map-Metric-Space :
    ( comp-short-map-Metric-Space A B B
      ( id-short-map-Metric-Space B)
      ( f)) ＝
    ( f)
  left-unit-law-comp-short-map-Metric-Space =
    left-unit-law-comp-short-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

  right-unit-law-comp-short-map-Metric-Space :
    ( comp-short-map-Metric-Space A A B
      ( f)
      ( id-short-map-Metric-Space A)) ＝
    ( f)
  right-unit-law-comp-short-map-Metric-Space =
    right-unit-law-comp-short-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
```

### Associativity of composition of short maps between metric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c l1d l2d : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  (D : Metric-Space l1d l2d)
  (h : short-map-Metric-Space C D)
  (g : short-map-Metric-Space B C)
  (f : short-map-Metric-Space A B)
  where

  associative-comp-short-map-Metric-Space :
    ( comp-short-map-Metric-Space A B D
      ( comp-short-map-Metric-Space B C D h g)
        ( f)) ＝
    ( comp-short-map-Metric-Space A C D
      ( h)
      ( comp-short-map-Metric-Space A B C g f))
  associative-comp-short-map-Metric-Space =
    associative-comp-short-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( pseudometric-Metric-Space C)
      ( pseudometric-Metric-Space D)
      ( h)
      ( g)
      ( f)
```

### Constant maps between metric spaces are short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (b : type-Metric-Space B)
  where

  is-short-map-const-Metric-Space :
    is-short-map-Metric-Space A B (const-map-Metric-Space A B b)
  is-short-map-const-Metric-Space =
    is-short-map-const-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( b)

  const-short-map-Metric-Space : short-map-Metric-Space A B
  const-short-map-Metric-Space =
    const-short-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( b)
```

### Any isometry between metric spaces is short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : map-Metric-Space A B)
  where

  is-short-map-is-isometry-Metric-Space :
    is-isometry-Metric-Space A B f →
    is-short-map-Metric-Space A B f
  is-short-map-is-isometry-Metric-Space =
    is-short-map-is-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
```

### The embedding of isometries of metric spaces into short maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  short-map-isometry-Metric-Space :
    isometry-Metric-Space A B → short-map-Metric-Space A B
  short-map-isometry-Metric-Space =
    short-map-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)

  is-emb-short-map-isometry-Metric-Space :
    is-emb short-map-isometry-Metric-Space
  is-emb-short-map-isometry-Metric-Space =
    is-emb-short-map-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)

  emb-short-map-isometry-Metric-Space :
    isometry-Metric-Space A B ↪ short-map-Metric-Space A B
  emb-short-map-isometry-Metric-Space =
    emb-short-map-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
```

## See also

- The
  [category of short maps on metric spaces](metric-spaces.category-of-metric-spaces-and-short-maps.md)

## External links

- [Short maps](https://ncatlab.org/nlab/show/short+map) at $n$Lab
- [Metric maps](https://en.wikipedia.org/wiki/Metric_map) at Wikipedia
