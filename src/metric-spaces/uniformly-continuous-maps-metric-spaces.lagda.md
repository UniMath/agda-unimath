# Uniformly continuous maps between metric spaces

```agda
module metric-spaces.uniformly-continuous-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import logic.functoriality-existential-quantification

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.continuity-of-maps-at-points-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulated-uniformly-continuous-maps-metric-spaces
open import metric-spaces.pointwise-continuous-maps-metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.short-maps-metric-spaces
```

</details>

## Idea

A [map](metric-spaces.maps-metric-spaces.md) `f` between
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y` is
{{#concept "uniformly continuous" Disambiguation="map between metric spaces" WDID=Q741865 WD="uniform continuity" Agda=is-uniformly-continuous-map-Metric-Space}}
if there [exists](foundation.existential-quantification.md) a
[modulus of uniform continuity](metric-spaces.modulated-uniformly-continuous-maps-metric-spaces.md)
for it.

## Definitions

### The property of being a uniformly continuous map

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : map-Metric-Space X Y)
  where

  is-uniformly-continuous-prop-map-Metric-Space : Prop (l1 ⊔ l2 ⊔ l4)
  is-uniformly-continuous-prop-map-Metric-Space =
    is-inhabited-Prop
      ( modulus-of-uniform-continuity-map-Metric-Space X Y f)

  is-uniformly-continuous-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-uniformly-continuous-map-Metric-Space =
    type-Prop is-uniformly-continuous-prop-map-Metric-Space
```

### The type of uniformly continuous maps between metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  where

  uniformly-continuous-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  uniformly-continuous-map-Metric-Space =
    type-subtype (is-uniformly-continuous-prop-map-Metric-Space X Y)

  map-uniformly-continuous-map-Metric-Space :
    uniformly-continuous-map-Metric-Space →
    map-Metric-Space X Y
  map-uniformly-continuous-map-Metric-Space = pr1

  is-uniformly-continuous-map-uniformly-continuous-map-Metric-Space :
    (f : uniformly-continuous-map-Metric-Space) →
    is-uniformly-continuous-map-Metric-Space
      ( X)
      ( Y)
      ( map-uniformly-continuous-map-Metric-Space f)
  is-uniformly-continuous-map-uniformly-continuous-map-Metric-Space =
    pr2

  uniformly-continuous-map-modulated-ucont-map-Metric-Space :
    modulated-ucont-map-Metric-Space X Y →
    uniformly-continuous-map-Metric-Space
  uniformly-continuous-map-modulated-ucont-map-Metric-Space (f , m) =
    (f , unit-trunc-Prop m)
```

## Properties

### The moduli of uniform continuity of a map form a set

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  where

  is-set-modulus-of-uniform-continuity-map-Metric-Space :
    (f : map-Metric-Space X Y) →
    is-set (modulus-of-uniform-continuity-map-Metric-Space X Y f)
  is-set-modulus-of-uniform-continuity-map-Metric-Space f =
    is-set-Σ
      ( is-set-function-type is-set-ℚ⁺)
      ( λ m →
        is-set-is-prop
          ( is-prop-type-Prop
            ( is-modulus-of-uniform-continuity-prop-map-Metric-Space
              ( X)
              ( Y)
              ( f)
              ( m))))

  modulus-of-uniform-continuity-set-map-Metric-Space :
    (f : map-Metric-Space X Y) → Set (l1 ⊔ l2 ⊔ l4)
  modulus-of-uniform-continuity-set-map-Metric-Space f =
    ( modulus-of-uniform-continuity-map-Metric-Space X Y f ,
      is-set-modulus-of-uniform-continuity-map-Metric-Space f)
```

### The identity map is uniformly continuous

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  is-uniformly-continuous-map-id-Metric-Space :
    is-uniformly-continuous-map-Metric-Space X X id
  is-uniformly-continuous-map-id-Metric-Space =
    intro-exists id (λ _ _ _ → id)
```

### The composition of uniformly continuous maps is uniformly continuous

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (Z : Metric-Space l5 l6)
  where

  abstract
    is-uniformly-continuous-map-comp-Metric-Space :
      (g : map-Metric-Space Y Z) →
      (f : map-Metric-Space X Y) →
      is-uniformly-continuous-map-Metric-Space Y Z g →
      is-uniformly-continuous-map-Metric-Space X Y f →
      is-uniformly-continuous-map-Metric-Space X Z (g ∘ f)
    is-uniformly-continuous-map-comp-Metric-Space g f =
      map-binary-trunc-Prop
        ( λ μg μf →
          pr2 (comp-modulated-ucont-map-Metric-Space X Y Z (g , μg) (f , μf)))

  comp-uniformly-continuous-map-Metric-Space :
    uniformly-continuous-map-Metric-Space Y Z →
    uniformly-continuous-map-Metric-Space X Y →
    uniformly-continuous-map-Metric-Space X Z
  comp-uniformly-continuous-map-Metric-Space g f =
    ( map-uniformly-continuous-map-Metric-Space Y Z g ∘
      map-uniformly-continuous-map-Metric-Space X Y f) ,
    ( is-uniformly-continuous-map-comp-Metric-Space
      ( map-uniformly-continuous-map-Metric-Space Y Z g)
      ( map-uniformly-continuous-map-Metric-Space X Y f)
      ( is-uniformly-continuous-map-uniformly-continuous-map-Metric-Space
        ( Y)
        ( Z)
        ( g))
      ( is-uniformly-continuous-map-uniformly-continuous-map-Metric-Space
        ( X)
        ( Y)
        ( f)))
```

### Short maps are uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Metric-Space l1 l2)
  (B : Metric-Space l3 l4)
  where

  abstract
    is-uniformly-continuous-map-is-short-map-Metric-Space :
      (f : map-Metric-Space A B) →
      is-short-map-Metric-Space A B f →
      is-uniformly-continuous-map-Metric-Space A B f
    is-uniformly-continuous-map-is-short-map-Metric-Space f H =
      intro-exists id (λ x d → H d x)

  uniformly-continuous-map-short-map-Metric-Space :
    short-map-Metric-Space A B →
    uniformly-continuous-map-Metric-Space A B
  uniformly-continuous-map-short-map-Metric-Space =
    tot is-uniformly-continuous-map-is-short-map-Metric-Space
```

### Isometries are uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  where

  abstract
    is-uniformly-continuous-map-is-isometry-Metric-Space :
      (f : map-Metric-Space A B) →
      is-isometry-Metric-Space A B f →
      is-uniformly-continuous-map-Metric-Space A B f
    is-uniformly-continuous-map-is-isometry-Metric-Space f =
      is-uniformly-continuous-map-is-short-map-Metric-Space A B f ∘
      is-short-map-is-isometry-Metric-Space A B f

  uniformly-continuous-map-isometry-Metric-Space :
    isometry-Metric-Space A B →
    uniformly-continuous-map-Metric-Space A B
  uniformly-continuous-map-isometry-Metric-Space =
    tot is-uniformly-continuous-map-is-isometry-Metric-Space
```

### Constant maps are uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  (b : type-Metric-Space B)
  where

  abstract
    is-uniformly-continuous-map-const-map-Metric-Space :
      is-uniformly-continuous-map-Metric-Space A B
        ( const-map-Metric-Space A B b)
    is-uniformly-continuous-map-const-map-Metric-Space =
      is-uniformly-continuous-map-is-short-map-Metric-Space A B
        ( const-map-Metric-Space A B b)
        ( is-short-map-const-Metric-Space A B b)

  const-uniformly-continuous-map-Metric-Space :
    uniformly-continuous-map-Metric-Space A B
  const-uniformly-continuous-map-Metric-Space =
    ( const-map-Metric-Space A B b ,
      is-uniformly-continuous-map-const-map-Metric-Space)
```

### Uniformly continuous maps are pointwise continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  where

  abstract
    is-pointwise-continuous-map-is-uniformly-continuous-map-Metric-Space :
      (f : map-Metric-Space X Y) →
      is-uniformly-continuous-map-Metric-Space X Y f →
      is-pointwise-continuous-map-Metric-Space X Y f
    is-pointwise-continuous-map-is-uniformly-continuous-map-Metric-Space
      f H x = map-trunc-Prop (λ (μ , is-mod-μ) → (μ , is-mod-μ x)) H

  pointwise-continuous-map-uniformly-continuous-map-Metric-Space :
    uniformly-continuous-map-Metric-Space X Y →
    pointwise-continuous-map-Metric-Space X Y
  pointwise-continuous-map-uniformly-continuous-map-Metric-Space (f , H) =
    ( f ,
      is-pointwise-continuous-map-is-uniformly-continuous-map-Metric-Space f H)
```

### The action on sequences of uniformly continuous maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : uniformly-continuous-map-Metric-Space X Y)
  where

  map-sequence-uniformly-continuous-map-Metric-Space :
    sequence-type-Metric-Space X → sequence-type-Metric-Space Y
  map-sequence-uniformly-continuous-map-Metric-Space =
    map-sequence (map-uniformly-continuous-map-Metric-Space X Y f)
```

### The Cartesian product of uniformly continuous maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (A : Metric-Space l1 l2)
  (X : Metric-Space l3 l4)
  (B : Metric-Space l5 l6)
  (Y : Metric-Space l7 l8)
  (f@(map-f , ucont-f) : uniformly-continuous-map-Metric-Space A X)
  (g@(map-g , ucont-g) : uniformly-continuous-map-Metric-Space B Y)
  where

  map-product-uniformly-continuous-map-Metric-Space :
    type-Metric-Space A × type-Metric-Space B →
    type-Metric-Space X × type-Metric-Space Y
  map-product-uniformly-continuous-map-Metric-Space = map-product map-f map-g

  abstract
    is-uniformly-continuous-map-product-uniformly-continuous-map-Metric-Space :
      is-uniformly-continuous-map-Metric-Space
        ( product-Metric-Space A B)
        ( product-Metric-Space X Y)
        ( map-product-uniformly-continuous-map-Metric-Space)
    is-uniformly-continuous-map-product-uniformly-continuous-map-Metric-Space =
      map-binary-trunc-Prop
        ( λ μf μg →
          pr2
            ( product-modulated-ucont-map-Metric-Space A X B Y
              ( map-f , μf)
              ( map-g , μg)))
        ( ucont-f)
        ( ucont-g)

  product-uniformly-continuous-map-Metric-Space :
    uniformly-continuous-map-Metric-Space
      ( product-Metric-Space A B)
      ( product-Metric-Space X Y)
  product-uniformly-continuous-map-Metric-Space =
    ( map-product-uniformly-continuous-map-Metric-Space ,
      is-uniformly-continuous-map-product-uniformly-continuous-map-Metric-Space)
```

## See also

- [Modulated uniformly continuous maps on metric spaces](metric-spaces.modulated-uniformly-continuous-maps-metric-spaces.md)
