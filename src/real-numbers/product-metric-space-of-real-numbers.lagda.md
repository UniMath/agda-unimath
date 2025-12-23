# The product metric space of real numbers

```agda
module real-numbers.product-metric-space-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.complete-metric-spaces
open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.metric-spaces

open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

For any type `I`, the product metric space of the real numbers over `I` is the
metric space over functions `I → ℝ` defined by the
[product metric](metric-spaces.dependent-products-metric-spaces.md).

## Definition

```agda
Π-metric-space-ℝ :
  {l1 : Level} → UU l1 → (l2 : Level) → Metric-Space (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Π-metric-space-ℝ I l = Π-Metric-Space I (λ _ → metric-space-ℝ l)

Π-complete-metric-space-ℝ :
  {l1 : Level} → UU l1 → (l2 : Level) →
  Complete-Metric-Space (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Π-complete-metric-space-ℝ I l =
  Π-Complete-Metric-Space I (λ _ → complete-metric-space-ℝ l)

abstract
  is-complete-Π-metric-space-ℝ :
    {l1 : Level} (I : UU l1) (l2 : Level) →
    is-complete-Metric-Space (Π-metric-space-ℝ I l2)
  is-complete-Π-metric-space-ℝ I l =
    is-complete-metric-space-Complete-Metric-Space
      ( Π-complete-metric-space-ℝ I l)
```
