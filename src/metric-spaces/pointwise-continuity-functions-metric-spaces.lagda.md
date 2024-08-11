# Pointwise continuity of functions between metric spaces

```agda
module metric-spaces.pointwise-continuity-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.sequences
open import foundation.universe-levels

open import metric-spaces.convergent-sequences-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.limits-sequences-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

Pointwise continuity of functions between metric spaces

## Definitions

### Pointwise continuity

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : fun-Metric-Space A B) (x : type-Metric-Space A)
  where

  is-pointwise-continuity-modulus-fun-Metric-Space : ℚ⁺ → ℚ⁺ → UU (l1 ⊔ l2)
  is-pointwise-continuity-modulus-fun-Metric-Space ε δ =
    (y : type-Metric-Space A) →
    is-in-neighbourhood-Metric-Space A δ x y →
    is-in-neighbourhood-Metric-Space B ε (f x) (f y)

  is-pointwise-continuous-fun-Metric-Space : UU (l1 ⊔ l2)
  is-pointwise-continuous-fun-Metric-Space =
    (ε : ℚ⁺) → Σ ℚ⁺ (is-pointwise-continuity-modulus-fun-Metric-Space ε)

module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : fun-Metric-Space A B) (x : type-Metric-Space A)
  (H : is-pointwise-continuous-fun-Metric-Space A B f x) (ε : ℚ⁺)
  where

  pt-continuity-modulus-fun-Metric-Space : ℚ⁺
  pt-continuity-modulus-fun-Metric-Space = pr1 (H ε)

  is-pointwise-continuity-modulus-pt-continuity-modulus-fun-Metric-Space :
    is-pointwise-continuity-modulus-fun-Metric-Space A B f x ε
      pt-continuity-modulus-fun-Metric-Space
  is-pointwise-continuity-modulus-pt-continuity-modulus-fun-Metric-Space =
    pr2 (H ε)
```

## Properties

### The image of a convergent sequence by a function continuous at the limit point converges to the image of the limit point

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : fun-Metric-Space A B) (u : convergent-sequence-Metric-Space A)
  where

  is-limit-pointwise-continuous-map-convergent-sequence-Metric-Space :
    is-pointwise-continuous-fun-Metric-Space A B f
      ( limit-convergent-sequence-Metric-Space A u) →
    is-limit-sequence-Metric-Space B
      ( map-sequence f (sequence-convergent-sequence-Metric-Space A u))
      ( f (limit-convergent-sequence-Metric-Space A u))
  is-limit-pointwise-continuous-map-convergent-sequence-Metric-Space H d =
    ( modulus-limit-sequence-Metric-Space A
      ( sequence-convergent-sequence-Metric-Space A u)
      ( limit-convergent-sequence-Metric-Space A u)
      ( is-limit-convergent-sequence-Metric-Space A u)
      ( pt-continuity-modulus-fun-Metric-Space A B f
        ( limit-convergent-sequence-Metric-Space A u)
        ( H)
        ( d))) ,
    ( λ n K →
      is-pointwise-continuity-modulus-pt-continuity-modulus-fun-Metric-Space
        ( A)
        ( B)
        ( f)
        ( limit-convergent-sequence-Metric-Space A u)
        ( H)
        ( d)
        ( sequence-convergent-sequence-Metric-Space A u n)
        ( is-modulus-modulus-limit-sequence-Metric-Space A
          ( sequence-convergent-sequence-Metric-Space A u)
          ( limit-convergent-sequence-Metric-Space A u)
          ( is-limit-convergent-sequence-Metric-Space A u)
          ( pt-continuity-modulus-fun-Metric-Space A B f
            ( limit-convergent-sequence-Metric-Space A u)
            ( H)
            ( d))
          ( n)
          ( K)))
```

### The composition of pointwise continuous functions is pointwise continuous

```agda
module _
  {l1 l2 l3 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (C : Metric-Space l3) (g : fun-Metric-Space B C) (f : fun-Metric-Space A B)
  (a : type-Metric-Space A)
  where

  preserves-pt-continuity-comp-fun-Metric-Space :
    is-pointwise-continuous-fun-Metric-Space B C g (f a) →
    is-pointwise-continuous-fun-Metric-Space A B f a →
    is-pointwise-continuous-fun-Metric-Space A C (g ∘ f) a
  preserves-pt-continuity-comp-fun-Metric-Space H K ε =
    ( pt-continuity-modulus-fun-Metric-Space A B f a K
      ( pt-continuity-modulus-fun-Metric-Space B C g (f a) H ε)) ,
    ( λ y I →
      pr2
        ( H ε)
        ( f y)
        ( pr2
          ( K (pt-continuity-modulus-fun-Metric-Space B C g (f a) H ε))
          ( y)
          ( I)))
```

## See also

- Uniformly continuous functions are defined in
  [`metric-spaces.uniform-continuity-functions-metric-spaces`](metric-spaces.uniform-continuity-functions-metric-spaces.md).
