# Uniformly continuous functions between metric spaces (WIP)

```agda
module metric-spaces.uniformly-continuous-functions-metric-spaces-WIP where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.continuous-functions-metric-spaces-WIP
open import metric-spaces.metric-spaces-WIP
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) `f` between
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y` is
{{#concept "uniformly continuous" Disambiguation="function between metric spaces" WDID=Q741865 WD="uniform continuity" Agda=is-uniformly-continuous-map-Metric-Space-WIP}}
if there exists a function `m : ℚ⁺ → ℚ⁺` such that for any `x : X`, whenever
`x'` is in an `m ε`-neighborhood of `x`, `f x'` is in an `ε`-neighborhood of
`f x`. The function `m` is called a modulus of uniform continuity of `f`.

## Definitions

### The property of being a uniformly continuous function

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space-WIP l1 l2)
  (Y : Metric-Space-WIP l3 l4)
  (f : type-function-Metric-Space-WIP X Y)
  where

  is-modulus-of-uniform-continuity-prop-function-Metric-Space-WIP :
    (ℚ⁺ → ℚ⁺) → Prop (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-uniform-continuity-prop-function-Metric-Space-WIP m =
    Π-Prop
      ( type-Metric-Space-WIP X)
      ( λ x →
        is-modulus-of-continuity-at-point-prop-function-Metric-Space-WIP
          X
          Y
          f
          x
          m)

  modulus-of-uniform-continuity-map-Metric-Space-WIP : UU (l1 ⊔ l2 ⊔ l4)
  modulus-of-uniform-continuity-map-Metric-Space-WIP =
    type-subtype is-modulus-of-uniform-continuity-prop-function-Metric-Space-WIP

  is-uniformly-continuous-prop-function-Metric-Space-WIP : Prop (l1 ⊔ l2 ⊔ l4)
  is-uniformly-continuous-prop-function-Metric-Space-WIP =
    is-inhabited-subtype-Prop
      is-modulus-of-uniform-continuity-prop-function-Metric-Space-WIP

  is-uniformly-continuous-function-Metric-Space-WIP : UU (l1 ⊔ l2 ⊔ l4)
  is-uniformly-continuous-function-Metric-Space-WIP =
    type-Prop is-uniformly-continuous-prop-function-Metric-Space-WIP
```

### The type of uniformly continuous functions between metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space-WIP l1 l2)
  (Y : Metric-Space-WIP l3 l4)
  where

  uniformly-continuous-function-Metric-Space-WIP : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  uniformly-continuous-function-Metric-Space-WIP =
    type-subtype (is-uniformly-continuous-prop-function-Metric-Space-WIP X Y)

  map-uniformly-continuous-function-Metric-Space-WIP :
    uniformly-continuous-function-Metric-Space-WIP →
    type-function-Metric-Space-WIP X Y
  map-uniformly-continuous-function-Metric-Space-WIP = pr1

  is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space-WIP :
    (f : uniformly-continuous-function-Metric-Space-WIP) →
    is-uniformly-continuous-function-Metric-Space-WIP
      ( X)
      ( Y)
      ( map-uniformly-continuous-function-Metric-Space-WIP f)
  is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space-WIP =
    pr2
```

## Properties

### Uniformly continuous functions are continuous at all points

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space-WIP l1 l2)
  (Y : Metric-Space-WIP l3 l4)
  (f : type-function-Metric-Space-WIP X Y)
  where

  is-continuous-at-point-is-uniformly-continuous-function-Metric-Space-WIP :
    is-uniformly-continuous-function-Metric-Space-WIP X Y f →
    (x : type-Metric-Space-WIP X) →
    is-continuous-at-point-function-Metric-Space-WIP X Y f x
  is-continuous-at-point-is-uniformly-continuous-function-Metric-Space-WIP H x =
    elim-exists
      ( is-continuous-at-point-prop-function-Metric-Space-WIP X Y f x)
      ( λ m K → intro-exists m (K x))
      ( H)
```

### The identity function is uniformly continuous

```agda
module _
  {l1 l2 : Level} (X : Metric-Space-WIP l1 l2)
  where

  is-uniformly-continuous-id-Metric-Space-WIP :
    is-uniformly-continuous-function-Metric-Space-WIP X X id
  is-uniformly-continuous-id-Metric-Space-WIP =
    intro-exists id (λ _ _ _ → id)
```

### The composition of uniformly continuous functions is uniformly continuous

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : Metric-Space-WIP l1 l2)
  (Y : Metric-Space-WIP l3 l4)
  (Z : Metric-Space-WIP l5 l6)
  where

  is-uniformly-continuous-comp-function-Metric-Space-WIP :
    (g : type-function-Metric-Space-WIP Y Z) →
    (f : type-function-Metric-Space-WIP X Y) →
    is-uniformly-continuous-function-Metric-Space-WIP Y Z g →
    is-uniformly-continuous-function-Metric-Space-WIP X Y f →
    is-uniformly-continuous-function-Metric-Space-WIP X Z (g ∘ f)
  is-uniformly-continuous-comp-function-Metric-Space-WIP g f H K =
    do
      mg , is-modulus-uniform-mg ← H
      mf , is-modulus-uniform-mf ← K
      intro-exists
        ( mf ∘ mg)
        ( λ x ε x' →
          is-modulus-uniform-mg (f x) ε (f x') ∘
          is-modulus-uniform-mf x (mg ε) x')
    where
      open
        do-syntax-trunc-Prop
          ( is-uniformly-continuous-prop-function-Metric-Space-WIP X Z (g ∘ f))

  comp-uniformly-continuous-function-Metric-Space-WIP :
    uniformly-continuous-function-Metric-Space-WIP Y Z →
    uniformly-continuous-function-Metric-Space-WIP X Y →
    uniformly-continuous-function-Metric-Space-WIP X Z
  comp-uniformly-continuous-function-Metric-Space-WIP g f =
    ( map-uniformly-continuous-function-Metric-Space-WIP Y Z g ∘
      map-uniformly-continuous-function-Metric-Space-WIP X Y f) ,
    ( is-uniformly-continuous-comp-function-Metric-Space-WIP
      ( map-uniformly-continuous-function-Metric-Space-WIP Y Z g)
      ( map-uniformly-continuous-function-Metric-Space-WIP X Y f)
      ( is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space-WIP
        ( Y)
        ( Z)
        ( g))
      ( is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space-WIP
        ( X)
        ( Y)
        ( f)))
```
