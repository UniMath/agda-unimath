# Uniformly continuous functions between metric spaces

```agda
module metric-spaces.uniformly-continuous-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

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
open import foundation.subtypes
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.continuous-functions-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulated-uniformly-continuous-functions-metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) `f` between
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y` is
{{#concept "uniformly continuous" Disambiguation="function between metric spaces" WDID=Q741865 WD="uniform continuity" Agda=is-uniformly-continuous-function-Metric-Space}}
if there [exists](foundation.existential-quantification.md) a
[modulus of uniform continuity](metric-spaces.modulated-uniformly-continuous-functions-metric-spaces.md)
for it.

## Definitions

### The property of being a uniformly continuous function

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y)
  where

  is-uniformly-continuous-prop-function-Metric-Space : Prop (l1 ⊔ l2 ⊔ l4)
  is-uniformly-continuous-prop-function-Metric-Space =
    is-inhabited-Prop
      (modulus-of-uniform-continuity-function-Metric-Space X Y f)

  is-uniformly-continuous-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-uniformly-continuous-function-Metric-Space =
    type-Prop is-uniformly-continuous-prop-function-Metric-Space
```

### The type of uniformly continuous functions between metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  where

  uniformly-continuous-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  uniformly-continuous-function-Metric-Space =
    type-subtype (is-uniformly-continuous-prop-function-Metric-Space X Y)

  map-uniformly-continuous-function-Metric-Space :
    uniformly-continuous-function-Metric-Space →
    type-function-Metric-Space X Y
  map-uniformly-continuous-function-Metric-Space = pr1

  is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space :
    (f : uniformly-continuous-function-Metric-Space) →
    is-uniformly-continuous-function-Metric-Space
      ( X)
      ( Y)
      ( map-uniformly-continuous-function-Metric-Space f)
  is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space =
    pr2

  uniformly-continuous-function-modulated-ucont-map-Metric-Space :
    modulated-ucont-map-Metric-Space X Y →
    uniformly-continuous-function-Metric-Space
  uniformly-continuous-function-modulated-ucont-map-Metric-Space (f , m) =
    (f , unit-trunc-Prop m)
```

## Properties

### Uniformly continuous functions are continuous everywhere

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y)
  where

  is-continuous-at-point-is-uniformly-continuous-function-Metric-Space :
    is-uniformly-continuous-function-Metric-Space X Y f →
    (x : type-Metric-Space X) →
    is-continuous-at-point-function-Metric-Space X Y f x
  is-continuous-at-point-is-uniformly-continuous-function-Metric-Space H x =
    rec-trunc-Prop
      ( is-continuous-at-point-prop-function-Metric-Space X Y f x)
      ( λ m →
        is-continuous-at-point-map-modulated-ucont-map-Metric-Space X Y
          ( f , m)
          ( x))
      ( H)
```

### The identity function is uniformly continuous

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  is-uniformly-continuous-id-Metric-Space :
    is-uniformly-continuous-function-Metric-Space X X id
  is-uniformly-continuous-id-Metric-Space =
    intro-exists id (λ _ _ _ → id)
```

### The composition of uniformly continuous functions is uniformly continuous

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (Z : Metric-Space l5 l6)
  where

  abstract
    is-uniformly-continuous-comp-function-Metric-Space :
      (g : type-function-Metric-Space Y Z) →
      (f : type-function-Metric-Space X Y) →
      is-uniformly-continuous-function-Metric-Space Y Z g →
      is-uniformly-continuous-function-Metric-Space X Y f →
      is-uniformly-continuous-function-Metric-Space X Z (g ∘ f)
    is-uniformly-continuous-comp-function-Metric-Space g f H K =
      let
        open
          do-syntax-trunc-Prop
            ( is-uniformly-continuous-prop-function-Metric-Space X Z (g ∘ f))
      in do
        (mg , is-modulus-uniform-mg) ← H
        (mf , is-modulus-uniform-mf) ← K
        intro-exists
          ( mf ∘ mg)
          ( λ x ε x' →
            is-modulus-uniform-mg (f x) ε (f x') ∘
            is-modulus-uniform-mf x (mg ε) x')

  comp-uniformly-continuous-function-Metric-Space :
    uniformly-continuous-function-Metric-Space Y Z →
    uniformly-continuous-function-Metric-Space X Y →
    uniformly-continuous-function-Metric-Space X Z
  comp-uniformly-continuous-function-Metric-Space g f =
    ( map-uniformly-continuous-function-Metric-Space Y Z g ∘
      map-uniformly-continuous-function-Metric-Space X Y f) ,
    ( is-uniformly-continuous-comp-function-Metric-Space
      ( map-uniformly-continuous-function-Metric-Space Y Z g)
      ( map-uniformly-continuous-function-Metric-Space X Y f)
      ( is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space
        ( Y)
        ( Z)
        ( g))
      ( is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space
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

  is-uniformly-continuous-is-short-function-Metric-Space :
    (f : type-function-Metric-Space A B) →
    is-short-function-Metric-Space A B f →
    is-uniformly-continuous-function-Metric-Space A B f
  is-uniformly-continuous-is-short-function-Metric-Space f H =
    intro-exists id (λ x d → H d x)

  uniformly-continuous-short-function-Metric-Space :
    short-function-Metric-Space A B →
    uniformly-continuous-function-Metric-Space A B
  uniformly-continuous-short-function-Metric-Space =
    tot is-uniformly-continuous-is-short-function-Metric-Space
```

### Isometries are uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  where

  is-uniformly-continuous-is-isometry-Metric-Space :
    (f : type-function-Metric-Space A B) →
    is-isometry-Metric-Space A B f →
    is-uniformly-continuous-function-Metric-Space A B f
  is-uniformly-continuous-is-isometry-Metric-Space f =
    is-uniformly-continuous-is-short-function-Metric-Space A B f ∘
    is-short-is-isometry-Metric-Space A B f

  uniformly-continuous-isometry-Metric-Space :
    isometry-Metric-Space A B →
    uniformly-continuous-function-Metric-Space A B
  uniformly-continuous-isometry-Metric-Space =
    tot is-uniformly-continuous-is-isometry-Metric-Space
```

### The Cartesian product of modulated uniformly continuous functions on metric spaces

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  (C : Metric-Space l5 l6) (D : Metric-Space l7 l8)
  where

  product-uniformly-continuous-function-Metric-Space :
    uniformly-continuous-function-Metric-Space A B →
    uniformly-continuous-function-Metric-Space C D →
    uniformly-continuous-function-Metric-Space
      ( product-Metric-Space A C)
      ( product-Metric-Space B D)
  product-uniformly-continuous-function-Metric-Space (f , ∃μf) (g , ∃μg) =
    ( map-product f g ,
      map-binary-trunc-Prop
        ( λ μf μg →
          pr2
            ( product-modulated-ucont-map-Metric-Space
              ( A)
              ( B)
              ( C)
              ( D)
              ( f , μf)
              ( g , μg)))
        ( ∃μf)
        ( ∃μg))
```

## See also

- [Modulated uniformly continuous functions on metric spaces](metric-spaces.modulated-uniformly-continuous-functions-metric-spaces.md)
