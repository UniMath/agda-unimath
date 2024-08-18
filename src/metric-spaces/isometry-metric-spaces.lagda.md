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
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) is an
{{#concept "isometry" Disambiguation="between metric spaces" Agda=is-isometry-Metric-Space}}
if it transports [neighbourhoods](metric-spaces.neighbourhood-relations.md).

## Definitions

### The property of being a isometry between metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B)
  where

  is-isometry-prop-function-Metric-Space : Prop (l1 ⊔ l2)
  is-isometry-prop-function-Metric-Space =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( type-Metric-Space A)
          ( λ x →
            Π-Prop
              ( type-Metric-Space A)
              ( λ y →
                iff-Prop
                  ( neighbourhood-Metric-Space A d x y)
                  ( neighbourhood-Metric-Space B d (f x) (f y)))))

  is-isometry-function-Metric-Space : UU (l1 ⊔ l2)
  is-isometry-function-Metric-Space =
    type-Prop is-isometry-prop-function-Metric-Space

  is-prop-is-isometry-function-Metric-Space :
    is-prop is-isometry-function-Metric-Space
  is-prop-is-isometry-function-Metric-Space =
    is-prop-type-Prop is-isometry-prop-function-Metric-Space
```

### The set of isometries between metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  where

  set-isometry-function-Metric-Space : Set (l1 ⊔ l2)
  set-isometry-function-Metric-Space =
    set-subset
      ( set-function-carrier-type-Metric-Space A B)
      ( is-isometry-prop-function-Metric-Space A B)

  isometry-function-Metric-Space : UU (l1 ⊔ l2)
  isometry-function-Metric-Space = type-Set set-isometry-function-Metric-Space

  is-set-isometry-function-Metric-Space : is-set isometry-function-Metric-Space
  is-set-isometry-function-Metric-Space =
    is-set-type-Set set-isometry-function-Metric-Space
```

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : isometry-function-Metric-Space A B)
  where

  map-isometry-function-Metric-Space : function-carrier-type-Metric-Space A B
  map-isometry-function-Metric-Space = pr1 f

  is-isometry-map-isometry-function-Metric-Space :
    is-isometry-function-Metric-Space
      A
      B
      map-isometry-function-Metric-Space
  is-isometry-map-isometry-function-Metric-Space = pr2 f
```

## Properties

### Two isometries are equal if their underlying maps are pointwise equal

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f g : isometry-function-Metric-Space A B)
  where

  eq-isometry-function-Metric-Space :
    ( (x : type-Metric-Space A) →
      Id
        ( map-isometry-function-Metric-Space A B f x)
        ( map-isometry-function-Metric-Space A B g x)) →
    Id f g
  eq-isometry-function-Metric-Space H =
    eq-type-subtype
      ( is-isometry-prop-function-Metric-Space A B)
      ( eq-htpy H)
```

### The identity function on a metric space is an isometry

```agda
module _
  {l : Level} (A : Metric-Space l)
  where

  is-isometry-id-Metric-Space :
    is-isometry-function-Metric-Space A A (id-Metric-Space A)
  is-isometry-id-Metric-Space d x y = id-iff

  isometry-id-Metric-Space : isometry-function-Metric-Space A A
  isometry-id-Metric-Space =
    id-Metric-Space A , is-isometry-id-Metric-Space
```

### The composition of isometries is an isometry

```agda
module _
  {l1 l2 l3 : Level}
  (A : Metric-Space l1)
  (B : Metric-Space l2)
  (C : Metric-Space l3)
  (g : function-carrier-type-Metric-Space B C)
  (f : function-carrier-type-Metric-Space A B)
  where

  preserves-isometry-comp-function-Metric-Space :
    is-isometry-function-Metric-Space B C g →
    is-isometry-function-Metric-Space A B f →
    is-isometry-function-Metric-Space A C (g ∘ f)
  preserves-isometry-comp-function-Metric-Space H K d x y =
    (H d (f x) (f y)) ∘iff (K d x y)
```

### The isometric composition of isometries

```agda
module _
  {l1 l2 l3 : Level}
  (A : Metric-Space l1)
  (B : Metric-Space l2)
  (C : Metric-Space l3)
  (g : isometry-function-Metric-Space B C)
  (f : isometry-function-Metric-Space A B)
  where

  comp-isometry-function-Metric-Space :
    isometry-function-Metric-Space A C
  comp-isometry-function-Metric-Space =
    ( map-isometry-function-Metric-Space B C g ∘
      map-isometry-function-Metric-Space A B f) ,
    ( preserves-isometry-comp-function-Metric-Space
      ( A)
      ( B)
      ( C)
      ( map-isometry-function-Metric-Space B C g)
      ( map-isometry-function-Metric-Space A B f)
      ( is-isometry-map-isometry-function-Metric-Space B C g)
      ( is-isometry-map-isometry-function-Metric-Space A B f))
```

### The inverse of an isometric equivalence is an isometry

```agda
module _
  {l1 l2 : Level}
  (A : Metric-Space l1)
  (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B)
  (I : is-isometry-function-Metric-Space A B f)
  (E : is-equiv f)
  where

  is-isometry-map-inv-equiv-Metric-Space :
    is-isometry-function-Metric-Space B A (map-inv-is-equiv E)
  is-isometry-map-inv-equiv-Metric-Space d x y =
    logical-equivalence-reasoning
      ( is-in-neighbourhood-Metric-Space B d x y)
      ↔ ( is-in-neighbourhood-Metric-Space B d
          ( f (map-inv-is-equiv E x))
          ( f (map-inv-is-equiv E y)))
        by
          binary-tr
            ( λ u v →
              ( is-in-neighbourhood-Metric-Space B d x y) ↔
              ( is-in-neighbourhood-Metric-Space B d u v))
            ( inv (is-section-map-inv-is-equiv E x))
            ( inv (is-section-map-inv-is-equiv E y))
            ( id-iff)
      ↔ ( is-in-neighbourhood-Metric-Space A d
          ( map-inv-is-equiv E x)
          (map-inv-is-equiv E y))
        by
          inv-iff
            ( I d (map-inv-is-equiv E x) (map-inv-is-equiv E y))
```

### Any isometry is short

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B)
  (H : is-isometry-function-Metric-Space A B f)
  where

  is-short-is-isometry-function-Metric-Space :
    is-short-function-Metric-Space A B f
  is-short-is-isometry-function-Metric-Space d x y =
    forward-implication (H d x y)
```
