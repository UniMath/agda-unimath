# The metric space of functions into the real numbers

```agda
module real-numbers.metric-space-of-functions-into-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.complete-metric-spaces
open import metric-spaces.dependent-products-complete-metric-spaces
open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.metric-spaces

open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

For any type `I`, the
{{#concept "metric space of functions into ℝ" Agda=function-into-ℝ-Metric-Space}}
`I → ℝ` is defined by the
[product metric](metric-spaces.dependent-products-metric-spaces.md).

## Definition

```agda
function-into-ℝ-Metric-Space :
  {l1 : Level} → UU l1 → (l2 : Level) → Metric-Space (l1 ⊔ lsuc l2) (l1 ⊔ l2)
function-into-ℝ-Metric-Space I l = Π-Metric-Space I (λ _ → metric-space-ℝ l)

function-into-ℝ-Complete-Metric-Space :
  {l1 : Level} → UU l1 → (l2 : Level) →
  Complete-Metric-Space (l1 ⊔ lsuc l2) (l1 ⊔ l2)
function-into-ℝ-Complete-Metric-Space I l =
  Π-Complete-Metric-Space I (λ _ → complete-metric-space-ℝ l)

abstract
  is-complete-function-into-ℝ-Metric-Space :
    {l1 : Level} (I : UU l1) (l2 : Level) →
    is-complete-Metric-Space (function-into-ℝ-Metric-Space I l2)
  is-complete-function-into-ℝ-Metric-Space I l =
    is-complete-metric-space-Complete-Metric-Space
      ( function-into-ℝ-Complete-Metric-Space I l)
```
