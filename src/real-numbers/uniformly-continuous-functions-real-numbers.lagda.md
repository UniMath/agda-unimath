# Uniformly continuous functions on the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniformly-continuous-functions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.propositions
open import foundation.subtypes
open import metric-spaces.metric-spaces
open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```
</details>

## Idea

A function from ℝ to ℝ is
{{#concept "uniformly continuous" Disambiguation="function from ℝ to ℝ" WDID=Q741865 WD="uniform continuity" Agda=uniformly-continuous-function-ℝ}}
if it is a
[uniformly continuous](metric-spaces.uniformly-continuous-functions-metric-spaces.md)
function from the
[metric space of ℝ](real-numbers.metric-space-of-real-numbers.md) to itself.

## Definition

```agda
is-uniformly-continuous-prop-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → Prop (lsuc l1 ⊔ l2)
is-uniformly-continuous-prop-ℝ {l1} {l2} =
  is-uniformly-continuous-prop-function-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)

is-uniformly-continuous-ℝ : {l1 l2 : Level} → (ℝ l1 → ℝ l2) → UU (lsuc l1 ⊔ l2)
is-uniformly-continuous-ℝ f = type-Prop (is-uniformly-continuous-prop-ℝ f)

uniformly-continuous-function-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
uniformly-continuous-function-ℝ l1 l2 =
  type-subtype (is-uniformly-continuous-prop-ℝ {l1} {l2})
```
