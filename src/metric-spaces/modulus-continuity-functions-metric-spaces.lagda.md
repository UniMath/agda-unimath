# Continuity modulus of functions between metric spaces

```agda
module metric-spaces.modulus-continuity-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.sequences
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.neighbourhood-relations
```

</details>

## Idea

Pointwise and unform continuity modulus of functions between metric spaces.

## Definitions

### Pointwise continuity modulus

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B) (x : type-Metric-Space A)
  where

  is-pt-continuity-modulus-function-Metric-Space : ℚ⁺ → ℚ⁺ → UU (l1 ⊔ l2)
  is-pt-continuity-modulus-function-Metric-Space ε δ =
    (y : type-Metric-Space A) →
    is-in-neighbourhood-Metric-Space A δ x y →
    is-in-neighbourhood-Metric-Space B ε (f x) (f y)

  is-prop-is-pt-continuity-modulus-function-Metric-Space :
    (ε δ : ℚ⁺) → is-prop (is-pt-continuity-modulus-function-Metric-Space ε δ)
  is-prop-is-pt-continuity-modulus-function-Metric-Space ε δ =
    is-prop-Π
      ( λ y →
        is-prop-Π
          ( λ I →
            is-prop-is-in-neighbourhood
              ( neighbourhood-Metric-Space B)
              ( ε)
              ( f x)
              ( f y)))

  is-pt-continuity-modulus-prop-function-Metric-Space : ℚ⁺ → ℚ⁺ → Prop (l1 ⊔ l2)
  is-pt-continuity-modulus-prop-function-Metric-Space ε δ =
    is-pt-continuity-modulus-function-Metric-Space ε δ ,
    is-prop-is-pt-continuity-modulus-function-Metric-Space ε δ
```

### Uniform continuity modulus

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : function-carrier-type-Metric-Space A B)
  where

  is-continuity-modulus-function-Metric-Space : ℚ⁺ → ℚ⁺ → UU (l1 ⊔ l2)
  is-continuity-modulus-function-Metric-Space ε δ =
    (x y : type-Metric-Space A) →
    is-in-neighbourhood-Metric-Space A δ x y →
    is-in-neighbourhood-Metric-Space B ε (f x) (f y)

  is-prop-is-continuity-modulus-function-Metric-Space :
    (ε δ : ℚ⁺) → is-prop (is-continuity-modulus-function-Metric-Space ε δ)
  is-prop-is-continuity-modulus-function-Metric-Space ε δ =
    is-prop-Π
      ( λ x →
        is-prop-Π
          ( λ y →
            is-prop-Π
              (λ I →
                is-prop-is-in-neighbourhood
                  ( neighbourhood-Metric-Space B)
                  ( ε)
                  ( f x)
                  ( f y))))

  is-continuity-modulus-prop-function-Metric-Space : ℚ⁺ → ℚ⁺ → Prop (l1 ⊔ l2)
  is-continuity-modulus-prop-function-Metric-Space ε δ =
    is-continuity-modulus-function-Metric-Space ε δ ,
    is-prop-is-continuity-modulus-function-Metric-Space ε δ
```
