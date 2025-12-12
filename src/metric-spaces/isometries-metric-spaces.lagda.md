# Isometries between metric spaces

```agda
module metric-spaces.isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.preimages-rational-neighborhood-relations
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
```

</details>

## Idea

A [map of metric spaces](metric-spaces.functions-metric-spaces.md) `f : A → B`
is an
{{#concept "isometry" Disambiguation="between metric spaces" Agda=is-isometry-Metric-Space}}
if the
[rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
on `A` is equivalent to the
[preimage](metric-spaces.preimages-rational-neighborhood-relations.md) under `f`
of the rational neighborhood relation on `B`. In other words, `f` is an isometry
if it is an [isometry](metric-spaces.isometries-pseudometric-spaces.md) between
the underlying [pseudometric spaces](metric-spaces.pseudometric-spaces.md).

## Definitions

### The property of being a isometry between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : type-function-Metric-Space A B)
  where

  is-isometry-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-isometry-prop-Metric-Space =
    is-isometry-prop-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
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
      ( set-function-Metric-Space A B)
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

  map-isometry-Metric-Space : type-function-Metric-Space A B
  map-isometry-Metric-Space = pr1 f

  is-isometry-map-isometry-Metric-Space :
    is-isometry-Metric-Space A B map-isometry-Metric-Space
  is-isometry-map-isometry-Metric-Space = pr2 f
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

  id-isometry-Metric-Space : isometry-Metric-Space A A
  id-isometry-Metric-Space =
    id-Metric-Space A , is-isometry-id-Metric-Space
```

### Equality of isometries in metric spaces is equivalent to homotopies between their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f g : isometry-Metric-Space A B)
  where

  htpy-isometry-Metric-Space : UU (l1 ⊔ l1')
  htpy-isometry-Metric-Space =
    map-isometry-Metric-Space A B f ~ map-isometry-Metric-Space A B g

  is-prop-htpy-isometry-Metric-Space :
    is-prop htpy-isometry-Metric-Space
  is-prop-htpy-isometry-Metric-Space =
    is-prop-Π
      ( λ x →
        is-set-type-Metric-Space B
          ( map-isometry-Metric-Space A B f x)
          ( map-isometry-Metric-Space A B g x))

  htpy-prop-isometry-Metric-Space : Prop (l1 ⊔ l1')
  htpy-prop-isometry-Metric-Space =
    ( htpy-isometry-Metric-Space , is-prop-htpy-isometry-Metric-Space)

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  {f g : isometry-Metric-Space A B}
  where

  equiv-eq-htpy-map-isometry-Metric-Space :
    (f ＝ g) ≃ htpy-isometry-Metric-Space A B f g
  equiv-eq-htpy-map-isometry-Metric-Space =
    equiv-eq-htpy-map-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)

  htpy-eq-map-isometry-Metric-Space :
    (f ＝ g) → htpy-isometry-Metric-Space A B f g
  htpy-eq-map-isometry-Metric-Space =
    map-equiv equiv-eq-htpy-map-isometry-Metric-Space

  eq-htpy-map-isometry-Metric-Space :
    htpy-isometry-Metric-Space A B f g → (f ＝ g)
  eq-htpy-map-isometry-Metric-Space =
    map-inv-equiv equiv-eq-htpy-map-isometry-Metric-Space
```

### Isometries preserve and reflect neighborhoods

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : isometry-Metric-Space A B)
  where

  preserves-neighborhoods-map-isometry-Metric-Space :
    (d : ℚ⁺) (x y : type-Metric-Space A) →
    neighborhood-Metric-Space A d x y →
    neighborhood-Metric-Space
      ( B)
      ( d)
      ( map-isometry-Metric-Space A B f x)
      ( map-isometry-Metric-Space A B f y)
  preserves-neighborhoods-map-isometry-Metric-Space d x y =
    forward-implication
      ( is-isometry-map-isometry-Metric-Space A B f d x y)

  reflects-neighborhoods-map-isometry-Metric-Space :
    (d : ℚ⁺) (x y : type-Metric-Space A) →
    neighborhood-Metric-Space
      ( B)
      ( d)
      ( map-isometry-Metric-Space A B f x)
      ( map-isometry-Metric-Space A B f y) →
    neighborhood-Metric-Space A d x y
  reflects-neighborhoods-map-isometry-Metric-Space d x y =
    backward-implication
      ( is-isometry-map-isometry-Metric-Space A B f d x y)
```

### Composition of isometries

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  where

  is-isometry-comp-is-isometry-Metric-Space :
    (g : type-function-Metric-Space B C) →
    (f : type-function-Metric-Space A B) →
    is-isometry-Metric-Space B C g →
    is-isometry-Metric-Space A B f →
    is-isometry-Metric-Space A C (g ∘ f)
  is-isometry-comp-is-isometry-Metric-Space g f H K d x y =
    H d (f x) (f y) ∘iff K d x y

  comp-isometry-Metric-Space :
    isometry-Metric-Space B C →
    isometry-Metric-Space A B →
    isometry-Metric-Space A C
  comp-isometry-Metric-Space =
    comp-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( pseudometric-Metric-Space C)
```

### Unit laws for composition of isometries between metric spaces

```agda
module _
  {l1a l2a l1b l2b : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (f : isometry-Metric-Space A B)
  where

  left-unit-law-comp-isometry-Metric-Space :
    ( comp-isometry-Metric-Space A B B
      ( id-isometry-Metric-Space B)
      ( f)) ＝
    ( f)
  left-unit-law-comp-isometry-Metric-Space =
    left-unit-law-comp-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

  right-unit-law-comp-isometry-Metric-Space :
    ( comp-isometry-Metric-Space A A B
      ( f)
      ( id-isometry-Metric-Space A)) ＝
    ( f)
  right-unit-law-comp-isometry-Metric-Space =
    right-unit-law-comp-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
```

### Associativity of composition of isometries between metric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c l1d l2d : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  (D : Metric-Space l1d l2d)
  (h : isometry-Metric-Space C D)
  (g : isometry-Metric-Space B C)
  (f : isometry-Metric-Space A B)
  where

  associative-comp-isometry-Metric-Space :
    ( comp-isometry-Metric-Space A B D
      ( comp-isometry-Metric-Space B C D h g)
      ( f)) ＝
    ( comp-isometry-Metric-Space A C D
      ( h)
      ( comp-isometry-Metric-Space A B C g f))
  associative-comp-isometry-Metric-Space =
    associative-comp-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( pseudometric-Metric-Space C)
      ( pseudometric-Metric-Space D)
      ( h)
      ( g)
      ( f)
```

### The inverse of an isometric equivalence is an isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : type-function-Metric-Space A B)
  (I : is-isometry-Metric-Space A B f)
  (E : is-equiv f)
  where

  is-isometry-map-inv-is-equiv-is-isometry-Metric-Space :
    is-isometry-Metric-Space B A (map-inv-is-equiv E)
  is-isometry-map-inv-is-equiv-is-isometry-Metric-Space =
    is-isometry-map-inv-is-equiv-is-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
      ( I)
      ( E)

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : isometry-Metric-Space A B)
  (E : is-equiv (map-isometry-Metric-Space A B f))
  where

  isometry-inv-is-equiv-isometry-Metric-Space :
    isometry-Metric-Space B A
  isometry-inv-is-equiv-isometry-Metric-Space =
    isometry-inv-is-equiv-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
      ( E)

  is-section-isometry-inv-is-equiv-isometry-Metric-Space :
    ( comp-isometry-Metric-Space
      B
      A
      B
      f
      isometry-inv-is-equiv-isometry-Metric-Space) ＝
    ( id-isometry-Metric-Space B)
  is-section-isometry-inv-is-equiv-isometry-Metric-Space =
    is-section-isometry-inv-is-equiv-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
      ( E)

  is-retraction-isometry-inv-is-equiv-isometry-Metric-Space :
    ( comp-isometry-Metric-Space
      A
      B
      A
      isometry-inv-is-equiv-isometry-Metric-Space
      f) ＝
    ( id-isometry-Metric-Space A)
  is-retraction-isometry-inv-is-equiv-isometry-Metric-Space =
    is-retraction-isometry-inv-is-equiv-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
      ( E)
```

### Isometries between metric spaces are embeddings

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : isometry-Metric-Space A B)
  where

  abstract
    is-injective-map-isometry-Metric-Space :
      is-injective (map-isometry-Metric-Space A B f)
    is-injective-map-isometry-Metric-Space H =
      eq-sim-Metric-Space
        ( A)
        ( _)
        ( _)
        ( λ d →
          backward-implication
            ( is-isometry-map-isometry-Metric-Space A B f d _ _)
            ( sim-eq-Metric-Space B _ _ H d))

    is-emb-map-isometry-Metric-Space :
      is-emb (map-isometry-Metric-Space A B f)
    is-emb-map-isometry-Metric-Space =
      is-emb-is-injective
        ( is-set-type-Metric-Space B)
        ( is-injective-map-isometry-Metric-Space)

  emb-map-isometry-Metric-Space : type-Metric-Space A ↪ type-Metric-Space B
  emb-map-isometry-Metric-Space =
    ( map-isometry-Metric-Space A B f ,
      is-emb-map-isometry-Metric-Space)
```
