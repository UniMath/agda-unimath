# Dependent products of complete metric spaces

```agda
module metric-spaces.dependent-products-complete-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-short-maps-metric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

The [dependent product](metric-spaces.dependent-products-metric-spaces.md) of
[complete](metric-spaces.complete-metric-spaces.md)
[metric spaces](metric-spaces.metric-spaces.md) is complete.

## Proof

### A product of complete metric spaces is complete

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space l1 l2)
  (Π-complete : (x : A) → is-complete-Metric-Space (P x))
  where

  limit-cauchy-approximation-Π-is-complete-Metric-Space :
    cauchy-approximation-Metric-Space (Π-Metric-Space A P) →
    type-Π-Metric-Space A P
  limit-cauchy-approximation-Π-is-complete-Metric-Space u x =
    limit-cauchy-approximation-Complete-Metric-Space
      ( P x , Π-complete x)
      ( ev-cauchy-approximation-Π-Metric-Space A P u x)

  is-limit-limit-cauchy-approximation-Π-is-complete-Metric-Space :
    (u : cauchy-approximation-Metric-Space (Π-Metric-Space A P)) →
    is-limit-cauchy-approximation-Metric-Space
      ( Π-Metric-Space A P)
      ( u)
      ( limit-cauchy-approximation-Π-is-complete-Metric-Space u)
  is-limit-limit-cauchy-approximation-Π-is-complete-Metric-Space u ε δ x =
    is-limit-limit-cauchy-approximation-Complete-Metric-Space
      ( P x , Π-complete x)
      ( ev-cauchy-approximation-Π-Metric-Space A P u x)
      ( ε)
      ( δ)

  is-complete-Π-Metric-Space :
    is-complete-Metric-Space (Π-Metric-Space A P)
  is-complete-Π-Metric-Space u =
    ( limit-cauchy-approximation-Π-is-complete-Metric-Space u ,
      is-limit-limit-cauchy-approximation-Π-is-complete-Metric-Space u)
```

### The complete product of complete metric spaces

```agda
module _
  {l l1 l2 : Level} (A : UU l) (C : A → Complete-Metric-Space l1 l2)
  where

  Π-Complete-Metric-Space : Complete-Metric-Space (l ⊔ l1) (l ⊔ l2)
  pr1 Π-Complete-Metric-Space =
    Π-Metric-Space A (metric-space-Complete-Metric-Space ∘ C)
  pr2 Π-Complete-Metric-Space =
    is-complete-Π-Metric-Space
      ( A)
      ( metric-space-Complete-Metric-Space ∘ C)
      ( is-complete-metric-space-Complete-Metric-Space ∘ C)
```
