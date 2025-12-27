# Limits of sequences in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.limits-sequences-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.isometry-addition-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.uniformly-continuous-functions-real-numbers
```

</details>

## Idea

On this page, we describe properties of
[limits of sequences](metric-spaces.limits-of-sequences-metric-spaces.md) in the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
is-limit-prop-sequence-ℝ : {l : Level} → sequence (ℝ l) → ℝ l → Prop l
is-limit-prop-sequence-ℝ {l} =
  is-limit-prop-sequence-Metric-Space (metric-space-ℝ l)

is-limit-sequence-ℝ : {l : Level} → sequence (ℝ l) → ℝ l → UU l
is-limit-sequence-ℝ {l} = is-limit-sequence-Metric-Space (metric-space-ℝ l)

has-limit-sequence-ℝ : {l : Level} → sequence (ℝ l) → UU (lsuc l)
has-limit-sequence-ℝ {l} = has-limit-sequence-Metric-Space (metric-space-ℝ l)
```

## Properties

### Any two limits of a sequence of real numbers are equal

```agda
module _
  {l : Level}
  (σ : sequence (ℝ l))
  where

  abstract
    eq-is-limit-sequence-ℝ :
      (a b : ℝ l) → is-limit-sequence-ℝ σ a → is-limit-sequence-ℝ σ b → a ＝ b
    eq-is-limit-sequence-ℝ =
      eq-limit-sequence-Metric-Space
        ( metric-space-ℝ l)
        ( σ)
```

### If two sequences have a limit, their sum has a limit equal to the sum of the limits

```agda
module _
  {l1 l2 : Level}
  {u : sequence (ℝ l1)}
  {v : sequence (ℝ l2)}
  {lim-u : ℝ l1}
  {lim-v : ℝ l2}
  (Hu : is-limit-sequence-ℝ u lim-u)
  (Hv : is-limit-sequence-ℝ v lim-v)
  where

  abstract
    preserves-limits-add-sequence-ℝ :
      is-limit-sequence-Metric-Space
        ( metric-space-ℝ (l1 ⊔ l2))
        ( binary-map-sequence add-ℝ u v)
        ( lim-u +ℝ lim-v)
    preserves-limits-add-sequence-ℝ =
      preserves-limits-sequences-modulated-ucont-map-Metric-Space
        ( product-Metric-Space (metric-space-ℝ l1) (metric-space-ℝ l2))
        ( metric-space-ℝ (l1 ⊔ l2))
        ( modulated-ucont-add-pair-ℝ l1 l2)
        ( pair-sequence u v)
        ( lim-u , lim-v)
        ( is-limit-pair-sequence-Metric-Space
          ( metric-space-ℝ l1)
          ( metric-space-ℝ l2)
          ( Hu)
          ( Hv))
```

### Uniformly continuous functions from `ℝ` to `ℝ` preserve limits

```agda
module _
  {l1 l2 : Level}
  (f : uniformly-continuous-function-ℝ l1 l2)
  (u : sequence (ℝ l1))
  (lim : ℝ l1)
  where

  abstract
    preserves-limits-sequence-uniformly-continuous-function-ℝ :
      is-limit-sequence-ℝ u lim →
      is-limit-sequence-ℝ
        ( map-sequence
          ( map-uniformly-continuous-function-ℝ f)
          ( u))
        ( map-uniformly-continuous-function-ℝ f lim)
    preserves-limits-sequence-uniformly-continuous-function-ℝ =
      preserves-limits-sequences-uniformly-continuous-map-Metric-Space
        ( metric-space-ℝ l1)
        ( metric-space-ℝ l2)
        ( f)
        ( u)
        ( lim)
```
