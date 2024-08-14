# Continuous of functions between metric spaces

```agda
module metric-spaces.continuous-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.convergent-sequences-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.limit-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pointwise-continuous-functions-metric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) is
{{#concept "continuous" Disambiguation="function between metric spaces"}} if it
is
[pointwise continuous](metric-spaces.pointwise-continuous-functions-metric-spaces.md)
at all points.

## Definitions

### Continuity of function between metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B)
  where

  is-continuous-prop-function-Metric-Space : Prop (l1 ⊔ l2)
  is-continuous-prop-function-Metric-Space =
    Π-Prop
      ( type-Metric-Space A)
      ( is-pt-continuous-prop-function-Metric-Space A B f)

  is-continuous-function-Metric-Space : UU (l1 ⊔ l2)
  is-continuous-function-Metric-Space =
    type-Prop is-continuous-prop-function-Metric-Space

  is-prop-is-continuous-function-Metric-Space :
    is-prop is-continuous-function-Metric-Space
  is-prop-is-continuous-function-Metric-Space =
    is-prop-type-Prop is-continuous-prop-function-Metric-Space
```

### The type of continuous functions between metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  where

  continuous-function-Metric-Space : UU (l1 ⊔ l2)
  continuous-function-Metric-Space =
    type-subtype (is-continuous-prop-function-Metric-Space A B)
```

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : continuous-function-Metric-Space A B)
  where

  map-continuous-function-Metric-Space : function-carrier-type-Metric-Space A B
  map-continuous-function-Metric-Space = pr1 f

  is-continuous-map-continuous-function-Metric-Space :
    (x : type-Metric-Space A) →
      is-pt-continuous-function-Metric-Space
        A
        B
        map-continuous-function-Metric-Space
        x
  is-continuous-map-continuous-function-Metric-Space = pr2 f
```

## Properties

### The identity function on a metric space is continuous

```agda
module _
  {l : Level} (A : Metric-Space l)
  where

  is-continuous-id-Metric-Space :
    is-continuous-function-Metric-Space A A (id-Metric-Space A)
  is-continuous-id-Metric-Space x ε = intro-exists ε (λ y H → H)

  continuous-id-Metric-Space : continuous-function-Metric-Space A A
  continuous-id-Metric-Space =
    id-Metric-Space A , is-continuous-id-Metric-Space
```

### The type of continuous functions between metric spaces is a set

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  where

  is-set-continuous-function-Metric-Space :
    is-set (continuous-function-Metric-Space A B)
  is-set-continuous-function-Metric-Space =
    is-set-type-subtype
      ( is-continuous-prop-function-Metric-Space A B)
      ( is-set-Π (λ x → is-set-type-Metric-Space B))

  set-continuous-function-Metric-Space : Set (l1 ⊔ l2)
  set-continuous-function-Metric-Space =
    continuous-function-Metric-Space A B ,
    is-set-continuous-function-Metric-Space
```

### The composition of continuous functions is continuous

```agda
module _
  {l1 l2 l3 : Level}
  (A : Metric-Space l1)
  (B : Metric-Space l2)
  (C : Metric-Space l3)
  (g : function-carrier-type-Metric-Space B C)
  (f : function-carrier-type-Metric-Space A B)
  where

  preserves-continuity-comp-function-Metric-Space :
    is-continuous-function-Metric-Space B C g →
    is-continuous-function-Metric-Space A B f →
    is-continuous-function-Metric-Space A C (g ∘ f)
  preserves-continuity-comp-function-Metric-Space H K a =
    preserves-pt-continuity-comp-function-Metric-Space
      ( A)
      ( B)
      ( C)
      ( g)
      ( f)
      ( a)
      ( H (f a))
      ( K a)
```

### The continuous composition of continuous functions

```agda
module _
  {l1 l2 l3 : Level}
  (A : Metric-Space l1)
  (B : Metric-Space l2)
  (C : Metric-Space l3)
  (g : continuous-function-Metric-Space B C)
  (f : continuous-function-Metric-Space A B)
  where

  comp-continuous-function-Metric-Space :
    continuous-function-Metric-Space A C
  comp-continuous-function-Metric-Space =
    ( map-continuous-function-Metric-Space B C g ∘
      map-continuous-function-Metric-Space A B f) ,
    ( preserves-continuity-comp-function-Metric-Space
      ( A)
      ( B)
      ( C)
      ( map-continuous-function-Metric-Space B C g)
      ( map-continuous-function-Metric-Space A B f)
      ( is-continuous-map-continuous-function-Metric-Space B C g)
      ( is-continuous-map-continuous-function-Metric-Space A B f))
```

### The image of a convergent sequence by a continuous function continuous converges to the image of the limit point

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B)
  (H : is-continuous-function-Metric-Space A B f)
  (u : convergent-sequence-Metric-Space A)
  where

  is-limit-continuous-map-convergent-sequence-Metric-Space :
    is-limit-sequence-Metric-Space B
      ( map-sequence f (sequence-convergent-sequence-Metric-Space A u))
      ( f (limit-convergent-sequence-Metric-Space A u))
  is-limit-continuous-map-convergent-sequence-Metric-Space =
    is-limit-pt-continuous-map-convergent-sequence-Metric-Space
      ( A)
      ( B)
      ( f)
      ( u)
      ( H (limit-convergent-sequence-Metric-Space A u))
```

## See also

- Uniformly continuous functions are defined in
  [`metric-spaces.uniform-continuity-functions-metric-spaces`](metric-spaces.uniform-continuity-functions-metric-spaces.md).
