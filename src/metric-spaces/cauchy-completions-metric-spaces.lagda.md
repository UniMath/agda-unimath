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
open import metric-spaces.cauchy-precompletions-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.complete-extensions-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limit-points-cauchy-precompletions-metric-spaces
open import metric-spaces.limit-points-extensions-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precomplete-extensions-metric-spaces
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy completion" Disambiguation="of metric space" Agda=cauchy-completion-Metric-Space}}
of a [metric space](metric-spaces.metric-spaces.md) `M` is an
[extension](metric-spaces.extensions-metric-spaces.md) `i : M → N` of `M` that
is both [Cauchy-dense](metric-spaces.cauchy-dense-extensions-metric-spaces.md)
(i.e. all points of `N` are
[limits](metric-spaces.limit-points-extensions-metric-spaces.md) of some
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
`M` under the
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

module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (C : cauchy-completion-Metric-Space l3 l4 M)
  where

  extension-cauchy-completion-Metric-Space :
    extension-Metric-Space l3 l4 M
  extension-cauchy-completion-Metric-Space = pr1 C

  is-cauchy-completion-extension-cauchy-completion-Metric-Space :
    is-cauchy-completion-extension-Metric-Space M
      extension-cauchy-completion-Metric-Space
  is-cauchy-completion-extension-cauchy-completion-Metric-Space = pr2 C

  metric-space-cauchy-completion-Metric-Space : Metric-Space l3 l4
  metric-space-cauchy-completion-Metric-Space =
    metric-space-extension-Metric-Space M
      extension-cauchy-completion-Metric-Space

  type-metric-space-cauchy-completion-Metric-Space : UU l3
  type-metric-space-cauchy-completion-Metric-Space =
    type-metric-space-extension-Metric-Space M
      extension-cauchy-completion-Metric-Space

  is-cauchy-dense-extension-cauchy-completion-Metric-Space :
    (y : type-metric-space-cauchy-completion-Metric-Space) →
    is-limit-point-extension-Metric-Space
      ( M)
      ( extension-cauchy-completion-Metric-Space)
      ( y)
  is-cauchy-dense-extension-cauchy-completion-Metric-Space =
    pr1 is-cauchy-completion-extension-cauchy-completion-Metric-Space

  is-complete-metric-space-cauchy-completion-Metric-Space :
    is-complete-Metric-Space metric-space-cauchy-completion-Metric-Space
  is-complete-metric-space-cauchy-completion-Metric-Space =
    pr2 is-cauchy-completion-extension-cauchy-completion-Metric-Space

  complete-extension-cauchy-completion-Metric-Space :
    complete-extension-Metric-Space l3 l4 M
  complete-extension-cauchy-completion-Metric-Space =
    ( extension-cauchy-completion-Metric-Space ,
      is-complete-metric-space-cauchy-completion-Metric-Space)

  precomplete-extension-cauchy-completion-Metric-Space :
    precomplete-extension-Metric-Space l3 l4 M
  precomplete-extension-cauchy-completion-Metric-Space =
    precomplete-complete-extension-Metric-Space
      ( M)
      ( complete-extension-cauchy-completion-Metric-Space)
```

## Properties

### The isometries between a Cauchy completion and the Cauchy precompletion of a metric space

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (C : cauchy-completion-Metric-Space l3 l4 M)
  where

  isometry-cauchy-precompletion-cauchy-completion-Metric-Space :
    isometry-Metric-Space
      ( metric-space-cauchy-completion-Metric-Space M C)
      ( cauchy-precompletion-Metric-Space M)
  isometry-cauchy-precompletion-cauchy-completion-Metric-Space =
    isometry-cauchy-precompletion-is-cauchy-dense-extension-Metric-Space
      ( M)
      ( extension-cauchy-completion-Metric-Space M C)
      ( is-cauchy-dense-extension-cauchy-completion-Metric-Space M C)

  map-cauchy-precompletion-cauchy-completion-Metric-Space :
    type-metric-space-cauchy-completion-Metric-Space M C →
    type-cauchy-precompletion-Metric-Space M
  map-cauchy-precompletion-cauchy-completion-Metric-Space =
    map-isometry-Metric-Space
      ( metric-space-cauchy-completion-Metric-Space M C)
      ( cauchy-precompletion-Metric-Space M)
      ( isometry-cauchy-precompletion-cauchy-completion-Metric-Space)

  isometry-cauchy-completion-cauchy-precompletion-Metric-Space :
    isometry-Metric-Space
      ( cauchy-precompletion-Metric-Space M)
      ( metric-space-cauchy-completion-Metric-Space M C)
  isometry-cauchy-completion-cauchy-precompletion-Metric-Space =
    isometry-cauchy-precompletion-precomplete-extension-Metric-Space
      ( M)
      ( precomplete-extension-cauchy-completion-Metric-Space M C)

  map-cauchy-completion-cauchy-precompletion-Metric-Space :
    type-cauchy-precompletion-Metric-Space M →
    type-metric-space-cauchy-completion-Metric-Space M C
  map-cauchy-completion-cauchy-precompletion-Metric-Space =
    map-isometry-Metric-Space
      ( cauchy-precompletion-Metric-Space M)
      ( metric-space-cauchy-completion-Metric-Space M C)
      ( isometry-cauchy-completion-cauchy-precompletion-Metric-Space)
```
