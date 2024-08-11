# Uniform continuity of functions between metric spaces

```agda
module metric-spaces.uniform-continuity-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pointwise-continuity-functions-metric-spaces
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

Uniform continuity of functions between metric spaces

## Definitions

### Uniform continuity

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : fun-Metric-Space A B)
  where

  is-continuity-modulus-fun-Metric-Space : ℚ⁺ → ℚ⁺ → UU (l1 ⊔ l2)
  is-continuity-modulus-fun-Metric-Space ε δ =
    (x y : type-Metric-Space A) →
    is-in-neighbourhood-Metric-Space A δ x y →
    is-in-neighbourhood-Metric-Space B ε (f x) (f y)

  is-uniformly-continuous-fun-Metric-Space : UU (l1 ⊔ l2)
  is-uniformly-continuous-fun-Metric-Space =
    (ε : ℚ⁺) → Σ ℚ⁺ (is-continuity-modulus-fun-Metric-Space ε)

module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : fun-Metric-Space A B)
  (H : is-uniformly-continuous-fun-Metric-Space A B f) (ε : ℚ⁺)
  where

  continuity-modulus-fun-Metric-Space : ℚ⁺
  continuity-modulus-fun-Metric-Space = pr1 (H ε)

  is-continuity-modulus-continuity-modulus-fun-Metric-Space :
    is-continuity-modulus-fun-Metric-Space A B f ε
      continuity-modulus-fun-Metric-Space
  is-continuity-modulus-continuity-modulus-fun-Metric-Space = pr2 (H ε)
```

## Properties

### Uniformly continuous functions are continuous at every points

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : fun-Metric-Space A B)
  where

  is-continuous-is-uniformly-continuous-fun-Metric-Space :
    is-uniformly-continuous-fun-Metric-Space A B f →
    (x : type-Metric-Space A) →
    is-pointwise-continuous-fun-Metric-Space A B f x
  is-continuous-is-uniformly-continuous-fun-Metric-Space H x ε =
    ( continuity-modulus-fun-Metric-Space A B f H ε) ,
    ( is-continuity-modulus-continuity-modulus-fun-Metric-Space A B f H ε x)
```

### Constant functions between metric spaces are uniformly continuous

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (b : type-Metric-Space B)
  where

  is-uniformly-continuous-constant-fun-Metric-Space :
    is-uniformly-continuous-fun-Metric-Space A B (λ _ → b)
  is-uniformly-continuous-constant-fun-Metric-Space ε =
    (ε , λ x y H → is-reflexive-neighbourhood-Metric-Space B ε b)
```

### The identity function on a metric space is uniformly continuous

```agda
module _
  {l : Level} (A : Metric-Space l)
  where

  is-uniformly-continuous-id-Metric-Space :
    is-uniformly-continuous-fun-Metric-Space A A id
  is-uniformly-continuous-id-Metric-Space ε = (ε , λ x y H → H)
```

### The composition of uniformly continuous functions is uniformly continuous

```agda
module _
  {l1 l2 l3 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (C : Metric-Space l3) (g : fun-Metric-Space B C) (f : fun-Metric-Space A B)
  where

  preserves-uniform-continuity-comp-fun-Metric-Space :
    is-uniformly-continuous-fun-Metric-Space B C g →
    is-uniformly-continuous-fun-Metric-Space A B f →
    is-uniformly-continuous-fun-Metric-Space A C (g ∘ f)
  preserves-uniform-continuity-comp-fun-Metric-Space H K ε =
    ( continuity-modulus-fun-Metric-Space A B f K
      ( continuity-modulus-fun-Metric-Space B C g H ε)) ,
    ( λ x y I →
      pr2
        ( H ε)
        ( f x)
        ( f y)
        ( pr2
          ( K (continuity-modulus-fun-Metric-Space B C g H ε))
          ( x)
          ( y)
          ( I)))
```

### Any function from a discrete metric space to a metric space is uniformly continuous

```agda
module _
  {l1 l2 : Level} (A : Set l1) (B : Metric-Space l2)
  (f : fun-Metric-Space (discrete-Metric-Space A) B)
  where

  is-uniformly-continuous-fun-discrete-Metric-Space :
    is-uniformly-continuous-fun-Metric-Space (discrete-Metric-Space A) B f
  is-uniformly-continuous-fun-discrete-Metric-Space ε =
    (ε , λ x y I → indistinguishable-eq-Metric-Space B (f x) (f y) (ap f I) ε)
```
