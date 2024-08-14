# Pointwise continuous of functions between metric spaces

```agda
module metric-spaces.pointwise-continuous-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.universe-levels

open import metric-spaces.convergent-sequences-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.limit-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulus-continuity-functions-metric-spaces
open import metric-spaces.modulus-limit-sequences-metric-spaces
```

</details>

## Idea

Pointwise continuity of functions between metric spaces

## Definitions

### Pointwise continuity

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B) (x : type-Metric-Space A)
  where

  is-pt-continuous-prop-function-Metric-Space : Prop (l1 ⊔ l2)
  is-pt-continuous-prop-function-Metric-Space =
    Π-Prop
      ( ℚ⁺)
      ( ∃ ℚ⁺ ∘ (is-pt-continuity-modulus-prop-function-Metric-Space A B f x))

  is-pt-continuous-function-Metric-Space : UU (l1 ⊔ l2)
  is-pt-continuous-function-Metric-Space =
    type-Prop is-pt-continuous-prop-function-Metric-Space

  is-prop-is-pt-continous-function-Metric-Space :
    is-prop is-pt-continuous-function-Metric-Space
  is-prop-is-pt-continous-function-Metric-Space =
    is-prop-type-Prop is-pt-continuous-prop-function-Metric-Space

module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B) (x : type-Metric-Space A)
  (H : is-pt-continuous-function-Metric-Space A B f x) (ε : ℚ⁺)
  where

  modulus-pt-continuity-function-Metric-Space :
    ║ Σ ( ℚ⁺)
        ( is-pt-continuity-modulus-function-Metric-Space A B f x ε) ║₋₁
  modulus-pt-continuity-function-Metric-Space = H ε
```

## Properties

### The identity function on a metric space is pointwise continuous at every point

```agda
module _
  {l : Level} (A : Metric-Space l) (x : type-Metric-Space A)
  where

  is-pt-continuous-id-Metric-Space :
    is-pt-continuous-function-Metric-Space A A (id-Metric-Space A) x
  is-pt-continuous-id-Metric-Space ε = intro-exists ε (λ y H → H)
```

### The composition of pointwise continuous functions is pointwise continuous

```agda
module _
  {l1 l2 l3 : Level}
  (A : Metric-Space l1)
  (B : Metric-Space l2)
  (C : Metric-Space l3)
  (g : function-carrier-type-Metric-Space B C)
  (f : function-carrier-type-Metric-Space A B)
  (a : type-Metric-Space A)
  where

  preserves-pt-continuity-comp-function-Metric-Space :
    is-pt-continuous-function-Metric-Space B C g (f a) →
    is-pt-continuous-function-Metric-Space A B f a →
    is-pt-continuous-function-Metric-Space A C (g ∘ f) a
  preserves-pt-continuity-comp-function-Metric-Space H K ε =
    elim-exists
      ( ∃ ( ℚ⁺)
          ( is-pt-continuity-modulus-prop-function-Metric-Space
            ( A)
            ( C)
            ( g ∘ f)
            ( a)
            ( ε)))
      ( λ δ I →
        elim-exists
          ( ∃ ( ℚ⁺)
            ( is-pt-continuity-modulus-prop-function-Metric-Space
              ( A)
              ( C)
              ( g ∘ f)
              ( a)
              ( ε)))
          ( λ δ' J → intro-exists δ' (λ y → I (f y) ∘ J y))
          ( K δ))
      ( H ε)
```

### The image of a convergent sequence by a function continuous at the limit point converges to the image of the limit point

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B)
  (u : convergent-sequence-Metric-Space A)
  where

  is-limit-pt-continuous-map-convergent-sequence-Metric-Space :
    is-pt-continuous-function-Metric-Space A B f
      ( limit-convergent-sequence-Metric-Space A u) →
    is-limit-sequence-Metric-Space B
      ( map-sequence f (sequence-convergent-sequence-Metric-Space A u))
      ( f (limit-convergent-sequence-Metric-Space A u))
  is-limit-pt-continuous-map-convergent-sequence-Metric-Space H d =
    elim-exists
      ( ∃ ( ℕ)
          ( is-modulus-limit-prop-sequence-Metric-Space
            ( B)
            ( map-sequence f (sequence-convergent-sequence-Metric-Space A u))
            ( f (limit-convergent-sequence-Metric-Space A u))
            ( d)))
      ( λ d' I →
        elim-exists
          ( ∃ ( ℕ)
              ( is-modulus-limit-prop-sequence-Metric-Space
                ( B)
                ( map-sequence
                  ( f)
                  ( sequence-convergent-sequence-Metric-Space A u))
                ( f (limit-convergent-sequence-Metric-Space A u))
                ( d)))
          ( λ N H →
            intro-exists
              ( N)
              ( λ k J →
                I (sequence-convergent-sequence-Metric-Space A u k) (H k J)))
          ( modulus-limit-convergent-sequence-Metric-Space A u d'))
      ( H d)
```

## See also

- Uniformly continuous functions are defined in
  [`metric-spaces.uniform-continuity-functions-metric-spaces`](metric-spaces.uniform-continuity-functions-metric-spaces.md).
