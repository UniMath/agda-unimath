# Limits of sequences in metric abelian groups

```agda
module analysis.limits-of-sequences-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups
open import foundation.universe-levels
open import metric-spaces.cartesian-products-metric-spaces
open import foundation.subtypes
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import foundation.dependent-pair-types
open import foundation.propositions
open import lists.sequences
open import analysis.sequences-metric-abelian-groups
open import metric-spaces.limits-of-sequences-metric-spaces
```

</details>

## Idea

## Definition

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  (u : sequence-type-Metric-Ab G)
  (lim : type-Metric-Ab G)
  where

  is-limit-modulus-prop-sequence-Metric-Ab : subtype l2 (ℚ⁺ → ℕ)
  is-limit-modulus-prop-sequence-Metric-Ab =
    is-limit-modulus-prop-sequence-Metric-Space (metric-space-Metric-Ab G) u lim

  is-limit-modulus-sequence-Metric-Ab : (ℚ⁺ → ℕ) → UU l2
  is-limit-modulus-sequence-Metric-Ab =
    is-in-subtype is-limit-modulus-prop-sequence-Metric-Ab

  is-limit-prop-sequence-Metric-Ab : Prop l2
  is-limit-prop-sequence-Metric-Ab =
    is-limit-prop-sequence-Metric-Space (metric-space-Metric-Ab G) u lim

  is-limit-sequence-Metric-Ab : UU l2
  is-limit-sequence-Metric-Ab = type-Prop is-limit-prop-sequence-Metric-Ab
```

## Properties

### The addition of sequences adds their limits

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  {u v : sequence-type-Metric-Ab G}
  {lim-u lim-v : type-Metric-Ab G}
  where

  abstract
    distributive-add-is-limit-sequence-Metric-Ab :
      is-limit-sequence-Metric-Ab G u lim-u →
      is-limit-sequence-Metric-Ab G v lim-v →
      is-limit-sequence-Metric-Ab
        ( G)
        ( add-sequence-type-Metric-Ab G u v)
        ( add-Metric-Ab G lim-u lim-v)
    distributive-add-is-limit-sequence-Metric-Ab is-lim-u is-lim-v =
      preserves-is-limit-modulated-ucont-map-sequence-Metric-Space
        ( product-Metric-Space
          ( metric-space-Metric-Ab G)
          ( metric-space-Metric-Ab G))
        ( metric-space-Metric-Ab G)
        ( modulated-ucont-add-Metric-Ab G)
        ( pair-sequence u v)
        ( lim-u , lim-v)
        ( is-limit-pair-sequence-Metric-Space
          ( metric-space-Metric-Ab G)
          ( metric-space-Metric-Ab G)
          ( is-lim-u)
          ( is-lim-v))
```

### The negation of a sequence negates its limit

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  {u : sequence-type-Metric-Ab G}
  {lim-u : type-Metric-Ab G}
  where

  abstract
    neg-is-limit-sequence-Metric-Ab :
      is-limit-sequence-Metric-Ab G u lim-u →
      is-limit-sequence-Metric-Ab
        ( G)
        ( neg-sequence-type-Metric-Ab G u)
        ( neg-Metric-Ab G lim-u)
    neg-is-limit-sequence-Metric-Ab =
      preserves-is-limit-isometry-sequence-Metric-Space
        ( metric-space-Metric-Ab G)
        ( metric-space-Metric-Ab G)
        ( isometry-neg-Metric-Ab G)
        ( u)
        ( lim-u)

```
