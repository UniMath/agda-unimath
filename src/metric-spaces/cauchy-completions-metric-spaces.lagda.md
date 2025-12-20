# Cauchy completions of metric spaces

```agda
module metric-spaces.cauchy-completions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-dense-extensions-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.complete-extensions-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precomplete-extensions-metric-spaces
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy completion" Disambiguation="of metric space" Agda=cauchy-completion-Metric-Space}}
of a [metric space](metric-spaces.metric-spaces.md) `M` is an [extension of a
metric space](metric-spaces.extensions-metric-spaces.md] `i : M → N` that is
both [Cauchy-dense](metric-spaces.cauchy-dense-extensions-metric-spaces.md)
(i.e. all Cauchy approximations in `M`
[converge](metric-spaces.convergent-cauchy-approximations-metric-spaces.md) in
`N` under the
[action](metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces.md)
of `i`) and [complete](metric-spaces.complete-extensions-metric-spaces.md) (i.e.
`N` is a [complete metric space](metric-spaces.complete-metric-spaces.md)).

## Definition

### The property of being a Cauchy completion of a metric space

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 M)
  where

  is-cauchy-completion-prop-extension-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-cauchy-completion-prop-extension-Metric-Space =
    product-Prop
      ( is-cauchy-dense-prop-extension-Metric-Space M E)
      ( is-complete-prop-extension-Metric-Space M E)

  is-cauchy-completion-extension-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-cauchy-completion-extension-Metric-Space =
    type-Prop is-cauchy-completion-prop-extension-Metric-Space

  is-prop-is-cauchy-completion-extension-Metric-Space :
    is-prop is-cauchy-completion-extension-Metric-Space
  is-prop-is-cauchy-completion-extension-Metric-Space =
    is-prop-type-Prop is-cauchy-completion-prop-extension-Metric-Space
```

### The type of Cauchy completions of a metric space

```agda
module _
  {l1 l2 : Level}
  (l3 l4 : Level)
  (M : Metric-Space l1 l2)
  where

  cauchy-completion-Metric-Space : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  cauchy-completion-Metric-Space =
    Σ ( extension-Metric-Space l3 l4 M)
      ( is-cauchy-completion-extension-Metric-Space M)
```
