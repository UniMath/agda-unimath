# Short functions between metric spaces

```agda
module metric-spaces.short-functions-metric-spaces where
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

open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.poset-of-rational-neighborhood-relations
open import metric-spaces.preimages-rational-neighborhood-relations
open import metric-spaces.short-functions-pseudometric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) `f` between two
[metric spaces](metric-spaces.metric-spaces.md) `A` and `B` is
{{#concept "short" Disambiguation="function between metric spaces" Agda=is-short-function-Metric-Space WD="metric map" WDID=Q2713824}}
if it's [short](metric-spaces.short-functions-pseudometric-spaces.md) between
their underlying [pseudometric spaces](metric-spaces.pseudometric-spaces.md).
That is, if the
[rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
on `A` is [finer](metric-spaces.poset-of-rational-neighborhood-relations.md)
than the [preimage](metric-spaces.preimages-rational-neighborhood-relations.md)
by `f` of the rational neighborhood relation on `B`. I.e., upper bounds on the
distance between two points in `A` are upper bounds of the distance between
their images in `B`.

## Definitions

### The property of being a short function between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : type-function-Metric-Space A B)
  where

  is-short-function-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-short-function-prop-Metric-Space =
    is-short-function-prop-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

  is-short-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-short-function-Metric-Space =
    type-Prop is-short-function-prop-Metric-Space

  is-prop-is-short-function-Metric-Space :
    is-prop is-short-function-Metric-Space
  is-prop-is-short-function-Metric-Space =
    is-prop-type-Prop is-short-function-prop-Metric-Space
```

### The set of short functions between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  short-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  short-function-Metric-Space =
    short-function-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)

  set-short-function-Metric-Space : Set (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  set-short-function-Metric-Space =
    set-subset
      ( set-function-Metric-Space A B)
      ( is-short-function-prop-Metric-Space A B)

  is-set-short-function-Metric-Space :
    is-set short-function-Metric-Space
  is-set-short-function-Metric-Space =
    is-set-type-Set set-short-function-Metric-Space

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-function-Metric-Space A B)
  where

  map-short-function-Metric-Space : type-function-Metric-Space A B
  map-short-function-Metric-Space =
    map-short-function-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

  is-short-map-short-function-Metric-Space :
    is-short-function-Metric-Space A B map-short-function-Metric-Space
  is-short-map-short-function-Metric-Space =
    is-short-map-short-function-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
```

## Properties

### The identity function on a metric space is short

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-short-id-Metric-Space :
    is-short-function-Metric-Space A A (id-Metric-Space A)
  is-short-id-Metric-Space =
    is-short-id-Pseudometric-Space
      ( pseudometric-Metric-Space A)

  short-id-Metric-Space : short-function-Metric-Space A A
  short-id-Metric-Space =
    short-id-Pseudometric-Space (pseudometric-Metric-Space A)
```

### Equality of short functions between metric spaces is characterized by homotopy of their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f g : short-function-Metric-Space A B)
  where

  equiv-eq-htpy-map-short-function-Metric-Space :
    ( f ＝ g) ≃
    ( map-short-function-Metric-Space A B f ~
      map-short-function-Metric-Space A B g)
  equiv-eq-htpy-map-short-function-Metric-Space =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-short-function-prop-Metric-Space A B) f g

  eq-htpy-map-short-function-Metric-Space :
    ( map-short-function-Metric-Space A B f ~
      map-short-function-Metric-Space A B g) →
    ( f ＝ g)
  eq-htpy-map-short-function-Metric-Space =
    map-inv-equiv equiv-eq-htpy-map-short-function-Metric-Space
```

### Composition of short functions

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  where

  is-short-comp-is-short-function-Metric-Space :
    (g : type-function-Metric-Space B C) →
    (f : type-function-Metric-Space A B) →
    is-short-function-Metric-Space B C g →
    is-short-function-Metric-Space A B f →
    is-short-function-Metric-Space A C (g ∘ f)
  is-short-comp-is-short-function-Metric-Space =
    is-short-comp-is-short-function-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( pseudometric-Metric-Space C)

  comp-short-function-Metric-Space :
    short-function-Metric-Space B C →
    short-function-Metric-Space A B →
    short-function-Metric-Space A C
  comp-short-function-Metric-Space =
    comp-short-function-Pseudometric-Space
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
  (f : short-function-Metric-Space A B)
  where

  left-unit-law-comp-short-function-Metric-Space :
    ( comp-short-function-Metric-Space A B B
      ( short-id-Metric-Space B)
      ( f)) ＝
    ( f)
  left-unit-law-comp-short-function-Metric-Space =
    left-unit-law-comp-short-function-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

  right-unit-law-comp-short-function-Metric-Space :
    ( comp-short-function-Metric-Space A A B
      ( f)
      ( short-id-Metric-Space A)) ＝
    ( f)
  right-unit-law-comp-short-function-Metric-Space =
    right-unit-law-comp-short-function-Pseudometric-Space
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
  (h : short-function-Metric-Space C D)
  (g : short-function-Metric-Space B C)
  (f : short-function-Metric-Space A B)
  where

  associative-comp-short-function-Metric-Space :
    ( comp-short-function-Metric-Space A B D
      ( comp-short-function-Metric-Space B C D h g)
        ( f)) ＝
    ( comp-short-function-Metric-Space A C D
      ( h)
      ( comp-short-function-Metric-Space A B C g f))
  associative-comp-short-function-Metric-Space =
    associative-comp-short-function-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( pseudometric-Metric-Space C)
      ( pseudometric-Metric-Space D)
      ( h)
      ( g)
      ( f)
```

### Constant functions between metric spaces are short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (b : type-Metric-Space B)
  where

  is-short-constant-function-Metric-Space :
    is-short-function-Metric-Space A B (λ _ → b)
  is-short-constant-function-Metric-Space =
    is-short-constant-function-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( b)

  short-constant-function-Metric-Space : short-function-Metric-Space A B
  short-constant-function-Metric-Space =
    short-constant-function-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( b)
```

### Any isometry between metric spaces is short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : type-function-Metric-Space A B)
  where

  is-short-is-isometry-Metric-Space :
    is-isometry-Metric-Space A B f →
    is-short-function-Metric-Space A B f
  is-short-is-isometry-Metric-Space =
    is-short-is-isometry-Pseudometric-Space
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

  short-isometry-Metric-Space :
    isometry-Metric-Space A B → short-function-Metric-Space A B
  short-isometry-Metric-Space =
    short-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)

  is-emb-short-isometry-Metric-Space :
    is-emb short-isometry-Metric-Space
  is-emb-short-isometry-Metric-Space =
    is-emb-short-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)

  emb-short-isometry-Metric-Space :
    isometry-Metric-Space A B ↪ short-function-Metric-Space A B
  emb-short-isometry-Metric-Space =
    emb-short-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
```

## See also

- The
  [category of short functions on metric spaces](metric-spaces.category-of-metric-spaces-and-short-functions.md)

## External links

- [Short maps](https://ncatlab.org/nlab/show/short+map) at $n$Lab
- [Metric maps](https://en.wikipedia.org/wiki/Metric_map) at Wikipedia
