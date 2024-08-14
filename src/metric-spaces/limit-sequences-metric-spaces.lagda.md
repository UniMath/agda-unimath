# Limits of sequences in metric spaces

```agda
module metric-spaces.limit-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.modulus-limit-sequences-metric-spaces
open import metric-spaces.neighbourhood-relations
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

A point `x` of a [metric space](metric-spaces.metric-spaces.md) `(X , B)` is a
{{#concept "limit" Disambiguation="of a sequence in a metric space" Agda=is-limit-sequence-Metric-Space}}
of a [sequence](metric-spaces.sequences-metric-spaces.md) `u` in `X` if for all
`d : ℚ⁺` there [merely exists](foundation.existential-quantification.md) some
[limit modulus](metric-spaces.modulus-limit-sequences-metric-spaces.md) of `u`
at the point `x` and distance `d`.

## Definitions

### Limits of sequences in metric spaces

```agda
module _
  {l : Level} (M : Metric-Space l) (u : sequence-Metric-Space M)
  (x : type-Metric-Space M)
  where

  is-limit-prop-sequence-Metric-Space : Prop l
  is-limit-prop-sequence-Metric-Space =
    Π-Prop ℚ⁺ (∃ ℕ ∘ (is-modulus-limit-prop-sequence-Metric-Space M u x))

  is-limit-sequence-Metric-Space : UU l
  is-limit-sequence-Metric-Space =
    type-Prop is-limit-prop-sequence-Metric-Space
```

## Properties

### Two limits of a sequence in a metric space are indistinguishable

```agda
module _
  {l : Level} (M : Metric-Space l) (u : sequence-Metric-Space M)
  (x y : type-Metric-Space M)
  where

  indistinguishable-limit-sequence-Metric-Space :
    is-limit-sequence-Metric-Space M u x →
    is-limit-sequence-Metric-Space M u y →
    is-indistinguishable-in-neighbourhood
      ( neighbourhood-Metric-Space M)
      ( x)
      ( y)
  indistinguishable-limit-sequence-Metric-Space H K d =
    elim-exists
      ( neighbourhood-Metric-Space M d x y)
      ( λ Ny J →
        elim-exists
          ( neighbourhood-Metric-Space M d x y)
          ( λ Nx I →
            tr
              ( λ d' → is-in-neighbourhood-Metric-Space M d' x y)
              ( left-diff-law-add-ℚ⁺
                ( mediant-zero-ℚ⁺ d)
                ( d)
                ( le-mediant-zero-ℚ⁺ d))
              ( is-triangular-neighbourhood-Metric-Space
                ( M)
                ( x)
                ( u (max-ℕ Nx Ny))
                ( y)
                ( le-diff-ℚ⁺ (mediant-zero-ℚ⁺ d) d (le-mediant-zero-ℚ⁺ d))
                ( mediant-zero-ℚ⁺ d)
                ( is-symmetric-neighbourhood-Metric-Space
                  ( M)
                  ( mediant-zero-ℚ⁺ d)
                  ( y)
                  ( u (max-ℕ Nx Ny))
                  ( J (max-ℕ Nx Ny) (right-leq-max-ℕ Nx Ny)))
                ( I (max-ℕ Nx Ny) (left-leq-max-ℕ Nx Ny))))
          ( H (le-diff-ℚ⁺ (mediant-zero-ℚ⁺ d) d (le-mediant-zero-ℚ⁺ d))))
      ( K (mediant-zero-ℚ⁺ d))
```

### Two limits of a sequence in a metric space are equal

```agda
module _
  {l : Level} (M : Metric-Space l) (u : sequence-Metric-Space M)
  (x y : type-Metric-Space M)
  where

  eq-limit-sequence-Metric-Space :
    is-limit-sequence-Metric-Space M u x →
    is-limit-sequence-Metric-Space M u y →
    x ＝ y
  eq-limit-sequence-Metric-Space H K =
    is-tight-neighbourhood-Metric-Space M x y
      (indistinguishable-limit-sequence-Metric-Space M u x y H K)
```

### Constant sequences in metric spaces have a limit

```agda
module _
  {l : Level} (M : Metric-Space l) (x : type-Metric-Space M)
  where

  is-limit-constant-sequence-Metric-Space :
    is-limit-sequence-Metric-Space M (constant-sequence-Metric-Space M x) x
  is-limit-constant-sequence-Metric-Space d =
    intro-exists
      ( zero-ℕ)
      ( λ n H → is-reflexive-neighbourhood-Metric-Space M d x)
```
