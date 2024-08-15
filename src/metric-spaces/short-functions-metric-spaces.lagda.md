# Short functions between metric spaces

```agda
module metric-spaces.short-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) is
{{#concept "short" Disambiguation="function between metric spaces" Agda=is-short-function-Metric-Space}}
if it preserves [neighbourhoods](metric-spaces.neighbourhood-relations.md).

## Definitions

### The property of being a short function between metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B)
  where

  is-short-prop-function-Metric-Space : Prop (l1 ⊔ l2)
  is-short-prop-function-Metric-Space =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( type-Metric-Space A)
          ( λ x →
            Π-Prop
              ( type-Metric-Space A)
              ( λ y →
                hom-Prop
                  ( neighbourhood-Metric-Space A d x y)
                  ( neighbourhood-Metric-Space B d (f x) (f y)))))

  is-short-function-Metric-Space : UU (l1 ⊔ l2)
  is-short-function-Metric-Space = type-Prop is-short-prop-function-Metric-Space

  is-prop-is-short-function-Metric-Space :
    is-prop is-short-function-Metric-Space
  is-prop-is-short-function-Metric-Space =
    is-prop-type-Prop is-short-prop-function-Metric-Space
```

### The set of short functions between metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  where

  set-short-function-Metric-Space : Set (l1 ⊔ l2)
  set-short-function-Metric-Space =
    set-subset
      ( set-function-carrier-type-Metric-Space A B)
      ( is-short-prop-function-Metric-Space A B)

  short-function-Metric-Space : UU (l1 ⊔ l2)
  short-function-Metric-Space = type-Set set-short-function-Metric-Space

  is-set-short-function-Metric-Space : is-set short-function-Metric-Space
  is-set-short-function-Metric-Space =
    is-set-type-Set set-short-function-Metric-Space
```

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : short-function-Metric-Space A B)
  where

  map-short-function-Metric-Space : function-carrier-type-Metric-Space A B
  map-short-function-Metric-Space = pr1 f

  is-short-map-short-function-Metric-Space :
    is-short-function-Metric-Space
      A
      B
      map-short-function-Metric-Space
  is-short-map-short-function-Metric-Space = pr2 f
```

## Properties

### Two short functions are equal if their underlying maps are pointwise equal

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f g : short-function-Metric-Space A B)
  where

  eq-short-function-Metric-Space :
    ( (x : type-Metric-Space A) →
      Id
        ( map-short-function-Metric-Space A B f x)
        ( map-short-function-Metric-Space A B g x)) →
    Id f g
  eq-short-function-Metric-Space H =
    eq-type-subtype
      ( is-short-prop-function-Metric-Space A B)
      ( eq-htpy H)
```

### The identity function on a metric space is short

```agda
module _
  {l : Level} (A : Metric-Space l)
  where

  is-short-id-Metric-Space :
    is-short-function-Metric-Space A A (id-Metric-Space A)
  is-short-id-Metric-Space d x y H = H

  short-id-Metric-Space : short-function-Metric-Space A A
  short-id-Metric-Space =
    id-Metric-Space A , is-short-id-Metric-Space
```

### The composition of short functions is short

```agda
module _
  {l1 l2 l3 : Level}
  (A : Metric-Space l1)
  (B : Metric-Space l2)
  (C : Metric-Space l3)
  (g : function-carrier-type-Metric-Space B C)
  (f : function-carrier-type-Metric-Space A B)
  where

  preserves-short-comp-function-Metric-Space :
    is-short-function-Metric-Space B C g →
    is-short-function-Metric-Space A B f →
    is-short-function-Metric-Space A C (g ∘ f)
  preserves-short-comp-function-Metric-Space H K d x y =
    H d (f x) (f y) ∘ K d x y
```

### The short composition of short functions

```agda
module _
  {l1 l2 l3 : Level}
  (A : Metric-Space l1)
  (B : Metric-Space l2)
  (C : Metric-Space l3)
  (g : short-function-Metric-Space B C)
  (f : short-function-Metric-Space A B)
  where

  comp-short-function-Metric-Space :
    short-function-Metric-Space A C
  comp-short-function-Metric-Space =
    ( map-short-function-Metric-Space B C g ∘
      map-short-function-Metric-Space A B f) ,
    ( preserves-short-comp-function-Metric-Space
      ( A)
      ( B)
      ( C)
      ( map-short-function-Metric-Space B C g)
      ( map-short-function-Metric-Space A B f)
      ( is-short-map-short-function-Metric-Space B C g)
      ( is-short-map-short-function-Metric-Space A B f))
```

### Any short map is uniformly continuous

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B)
  (H : is-short-function-Metric-Space A B f)
  where

  is-uniformly-continuous-is-short-function-Metric-Space :
    is-uniformly-continuous-function-Metric-Space A B f
  is-uniformly-continuous-is-short-function-Metric-Space ε =
    intro-exists ε (H ε)
```

### Constant functions between metric spaces are short

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (b : type-Metric-Space B)
  where

  is-short-constant-function-Metric-Space :
    is-short-function-Metric-Space A B (λ _ → b)
  is-short-constant-function-Metric-Space ε x y H =
    is-reflexive-neighbourhood-Metric-Space B ε b
```

## See also

- [Short maps](https://ncatlab.org/nlab/show/short+map) at $n$Lab
