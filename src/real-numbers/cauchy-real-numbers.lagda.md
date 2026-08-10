# The Cauchy real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.cauchy-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-additive-group-of-rational-numbers
open import analysis.metric-quotients-cauchy-pseudocompletions-metric-abelian-groups

open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.binary-relations
open import foundation.embeddings
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

The {{#concept "Cauchy real numbers" Agda=cauchy-ℝ}} are the
[metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md) of
the
[Cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletions-of-metric-spaces.md)
of the
[metric space of rational numbers](metric-spaces.metric-space-of-rational-numbers.md).

The Cauchy real numbers are equivalent to the
[Dedekind real numbers](real-numbers.dedekind-real-numbers.md) in the presence
of [excluded middle](foundation.law-of-excluded-middle.md) or
[countable choice](foundation.axiom-of-countable-choice.md) equivalent
(Corollary 11.4.3 of {{#cite UF13}}), but not necessarily otherwise.

## Definition

```agda
cauchy-approximation-metric-space-ℚ : UU lzero
cauchy-approximation-metric-space-ℚ =
  cauchy-approximation-Metric-Space metric-space-ℚ

cauchy-pseudocompletion-metric-space-ℚ : Pseudometric-Space lzero lzero
cauchy-pseudocompletion-metric-space-ℚ =
  cauchy-pseudocompletion-Metric-Space metric-space-ℚ

sim-prop-cauchy-pseudocompletion-metric-space-ℚ :
  Relation-Prop lzero cauchy-approximation-metric-space-ℚ
sim-prop-cauchy-pseudocompletion-metric-space-ℚ =
  sim-prop-Pseudometric-Space cauchy-pseudocompletion-metric-space-ℚ

sim-cauchy-pseudocompletion-metric-space-ℚ :
  Relation lzero cauchy-approximation-metric-space-ℚ
sim-cauchy-pseudocompletion-metric-space-ℚ =
  sim-Pseudometric-Space cauchy-pseudocompletion-metric-space-ℚ

neighborhood-cauchy-pseudocompletion-metric-space-ℚ :
  ℚ⁺ → Relation lzero cauchy-approximation-metric-space-ℚ
neighborhood-cauchy-pseudocompletion-metric-space-ℚ =
  neighborhood-Pseudometric-Space cauchy-pseudocompletion-metric-space-ℚ

metric-space-cauchy-ℝ : Metric-Space lzero lzero
metric-space-cauchy-ℝ =
  metric-quotient-cauchy-pseudocompletion-Metric-Ab metric-ab-add-ℚ

pseudometric-space-cauchy-ℝ : Pseudometric-Space lzero lzero
pseudometric-space-cauchy-ℝ =
  pseudometric-Metric-Space metric-space-cauchy-ℝ

set-cauchy-ℝ : Set lzero
set-cauchy-ℝ = set-Metric-Space metric-space-cauchy-ℝ

cauchy-ℝ : UU lzero
cauchy-ℝ = type-Set set-cauchy-ℝ

neighborhood-prop-cauchy-ℝ : Rational-Neighborhood-Relation lzero cauchy-ℝ
neighborhood-prop-cauchy-ℝ =
  neighborhood-prop-Metric-Space metric-space-cauchy-ℝ

neighborhood-cauchy-ℝ : ℚ⁺ → Relation lzero cauchy-ℝ
neighborhood-cauchy-ℝ =
  neighborhood-Metric-Space metric-space-cauchy-ℝ
```

### The map from the rational numbers to the Cauchy real numbers

```agda
isometry-cauchy-real-ℚ :
  isometry-Metric-Space metric-space-ℚ metric-space-cauchy-ℝ
isometry-cauchy-real-ℚ =
  isometry-in-metric-quotient-cauchy-pseudocompletion-Metric-Ab metric-ab-add-ℚ

emb-cauchy-real-ℚ : ℚ ↪ cauchy-ℝ
emb-cauchy-real-ℚ =
  emb-map-isometry-Metric-Space
    ( metric-space-ℚ)
    ( metric-space-cauchy-ℝ)
    ( isometry-cauchy-real-ℚ)

cauchy-real-ℚ : ℚ → cauchy-ℝ
cauchy-real-ℚ = map-emb emb-cauchy-real-ℚ
```

### Important Cauchy real numbers

```agda
zero-cauchy-ℝ : cauchy-ℝ
zero-cauchy-ℝ = cauchy-real-ℚ zero-ℚ

one-cauchy-ℝ : cauchy-ℝ
one-cauchy-ℝ = cauchy-real-ℚ one-ℚ
```

### The map from Cauchy approximations in ℚ to the Cauchy real numbers

```agda
isometry-cauchy-real-cauchy-approximation-ℚ :
  isometry-Pseudometric-Space
    ( cauchy-pseudocompletion-metric-space-ℚ)
    ( pseudometric-space-cauchy-ℝ)
isometry-cauchy-real-cauchy-approximation-ℚ =
  isometry-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
    ( metric-ab-add-ℚ)

cauchy-real-cauchy-approximation-ℚ :
  cauchy-approximation-Metric-Space metric-space-ℚ → cauchy-ℝ
cauchy-real-cauchy-approximation-ℚ =
  map-isometry-Pseudometric-Space
    ( cauchy-pseudocompletion-Metric-Space metric-space-ℚ)
    ( pseudometric-space-cauchy-ℝ)
    ( isometry-cauchy-real-cauchy-approximation-ℚ)

is-isometry-cauchy-real-cauchy-approximation-ℚ :
  is-isometry-Pseudometric-Space
    ( cauchy-pseudocompletion-metric-space-ℚ)
    ( pseudometric-space-cauchy-ℝ)
    ( cauchy-real-cauchy-approximation-ℚ)
is-isometry-cauchy-real-cauchy-approximation-ℚ =
  is-isometry-map-isometry-Pseudometric-Space
    ( cauchy-pseudocompletion-Metric-Space metric-space-ℚ)
    ( pseudometric-space-cauchy-ℝ)
    ( isometry-cauchy-real-cauchy-approximation-ℚ)
```
