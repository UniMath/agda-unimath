# Uniformly continuous functions between metric spaces

```agda
module metric-spaces.uniformly-continuous-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.continuous-functions-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulus-continuity-functions-metric-spaces
open import metric-spaces.pointwise-continuous-functions-metric-spaces
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

Uniform continuity of functions between metric spaces.

## Definitions

### The property of being a uniformly continuous function between metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B)
  where

  is-uniformly-continuous-prop-function-Metric-Space : Prop (l1 ⊔ l2)
  is-uniformly-continuous-prop-function-Metric-Space =
    Π-Prop
      ( ℚ⁺)
      ( ∃ ℚ⁺ ∘ is-continuity-modulus-prop-function-Metric-Space A B f)

  is-uniformly-continuous-function-Metric-Space : UU (l1 ⊔ l2)
  is-uniformly-continuous-function-Metric-Space =
    type-Prop is-uniformly-continuous-prop-function-Metric-Space

  is-prop-is-uniformly-continuous-function-Metric-Space :
    is-prop is-uniformly-continuous-function-Metric-Space
  is-prop-is-uniformly-continuous-function-Metric-Space =
    is-prop-type-Prop is-uniformly-continuous-prop-function-Metric-Space
```

### The set of uniformly continuous functions between metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  where

  set-uniformly-continuous-function-Metric-Space : Set (l1 ⊔ l2)
  set-uniformly-continuous-function-Metric-Space =
    set-subset
      ( set-function-carrier-type-Metric-Space A B)
      ( is-uniformly-continuous-prop-function-Metric-Space A B)

  uniformly-continuous-function-Metric-Space : UU (l1 ⊔ l2)
  uniformly-continuous-function-Metric-Space =
    type-Set set-uniformly-continuous-function-Metric-Space

  is-set-uniformly-continuous-function-Metric-Space :
    is-set uniformly-continuous-function-Metric-Space
  is-set-uniformly-continuous-function-Metric-Space =
    is-set-type-Set set-uniformly-continuous-function-Metric-Space
```

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : uniformly-continuous-function-Metric-Space A B)
  where

  map-uniformly-continuous-function-Metric-Space :
    function-carrier-type-Metric-Space A B
  map-uniformly-continuous-function-Metric-Space = pr1 f

  is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space :
    is-uniformly-continuous-function-Metric-Space
      A
      B
      map-uniformly-continuous-function-Metric-Space
  is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space =
    pr2 f
```

## Properties

### Uniformly continuous functions are continuous at every point

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B)
  where

  is-continuous-is-uniformly-continuous-function-Metric-Space :
    is-uniformly-continuous-function-Metric-Space A B f →
    is-continuous-function-Metric-Space A B f
  is-continuous-is-uniformly-continuous-function-Metric-Space H x ε =
    elim-exists
      ( ∃ ℚ⁺ (is-pt-continuity-modulus-prop-function-Metric-Space A B f x ε))
      ( λ d H → intro-exists d (H x))
      ( H ε)
```

### Constant functions between metric spaces are uniformly continuous

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (b : type-Metric-Space B)
  where

  is-uniformly-continuous-constant-function-Metric-Space :
    is-uniformly-continuous-function-Metric-Space A B (λ _ → b)
  is-uniformly-continuous-constant-function-Metric-Space ε =
    intro-exists ε (λ x y H → is-reflexive-neighbourhood-Metric-Space B ε b)
```

### Two uniformly continuous functions are equal if their underlying maps are pointwise equal

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f g : uniformly-continuous-function-Metric-Space A B)
  where

  eq-uniformly-continuous-function-Metric-Space :
    ( (x : type-Metric-Space A) →
      Id
        ( map-uniformly-continuous-function-Metric-Space A B f x)
        ( map-uniformly-continuous-function-Metric-Space A B g x)) →
    Id f g
  eq-uniformly-continuous-function-Metric-Space H =
    eq-type-subtype
      ( is-uniformly-continuous-prop-function-Metric-Space A B)
      ( eq-htpy H)
```

### The identity function on a metric space is uniformly continuous

```agda
module _
  {l : Level} (A : Metric-Space l)
  where

  is-uniformly-continuous-id-Metric-Space :
    is-uniformly-continuous-function-Metric-Space A A id
  is-uniformly-continuous-id-Metric-Space ε = intro-exists ε (λ x y H → H)

  uniformly-continuous-id-Metric-Space :
    uniformly-continuous-function-Metric-Space A A
  uniformly-continuous-id-Metric-Space =
    id-Metric-Space A ,
    is-uniformly-continuous-id-Metric-Space
```

### The composition of uniformly continuous functions is uniformly continuous

```agda
module _
  {l1 l2 l3 : Level}
  (A : Metric-Space l1)
  (B : Metric-Space l2)
  (C : Metric-Space l3)
  (g : function-carrier-type-Metric-Space B C)
  (f : function-carrier-type-Metric-Space A B)
  where

  preserves-uniform-continuity-comp-function-Metric-Space :
    is-uniformly-continuous-function-Metric-Space B C g →
    is-uniformly-continuous-function-Metric-Space A B f →
    is-uniformly-continuous-function-Metric-Space A C (g ∘ f)
  preserves-uniform-continuity-comp-function-Metric-Space H K ε =
    elim-exists
      ( ∃ ( ℚ⁺)
          ( is-continuity-modulus-prop-function-Metric-Space A C (g ∘ f) ε))
      ( λ δ I →
        elim-exists
          ( ∃ ( ℚ⁺)
              ( is-continuity-modulus-prop-function-Metric-Space A C (g ∘ f) ε))
          ( λ δ' J → intro-exists δ' (λ x y → I (f x) (f y) ∘ (J x y)))
          ( K δ))
      ( H ε)
```

### The uniformly continuous composition of uniformly continuous functions

```agda
module _
  {l1 l2 l3 : Level}
  (A : Metric-Space l1)
  (B : Metric-Space l2)
  (C : Metric-Space l3)
  (g : uniformly-continuous-function-Metric-Space B C)
  (f : uniformly-continuous-function-Metric-Space A B)
  where

  comp-uniformly-continuous-function-Metric-Space :
    uniformly-continuous-function-Metric-Space A C
  comp-uniformly-continuous-function-Metric-Space =
    ( map-uniformly-continuous-function-Metric-Space B C g ∘
      map-uniformly-continuous-function-Metric-Space A B f) ,
    ( preserves-uniform-continuity-comp-function-Metric-Space
      ( A)
      ( B)
      ( C)
      ( map-uniformly-continuous-function-Metric-Space B C g)
      ( map-uniformly-continuous-function-Metric-Space A B f)
      ( is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space
        ( B)
        ( C)
        ( g))
      ( is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space
        ( A)
        ( B)
        ( f)))
```

### Any function from a discrete metric space to a metric space is uniformly continuous

```agda
module _
  {l1 l2 : Level} (A : Set l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space (discrete-Metric-Space A) B)
  where

  is-uniformly-continuous-function-discrete-Metric-Space :
    is-uniformly-continuous-function-Metric-Space (discrete-Metric-Space A) B f
  is-uniformly-continuous-function-discrete-Metric-Space ε =
    intro-exists
      ( ε)
      ( λ x y I → indistinguishable-eq-Metric-Space B (f x) (f y) (ap f I) ε)
```
