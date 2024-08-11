# Limits of sequences in metric spaces

```agda
module metric-spaces.limits-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.neighbourhood-relations
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

A point `x` of a [metric space](metric-spaces.metric-spaces.md) `A` is a
{{#concept "limit" Disambiguation="of a sequence in a metric space" Agda=is-limit-sequence-Metric-Space}}
of a [sequence](metric-spaces.sequences-metric-spaces.md) `u` in `A` if all
neighbourhoods of `x` asymptotically contain all terms of `u`.

## Definitions

### Limits of sequences in metric spaces

```agda
module _
  {l : Level} (M : Metric-Space l) (u : sequence-Metric-Space M)
  (x : type-Metric-Space M)
  where

  is-modulus-limit-prop-sequence-Metric-Space : (d : ℚ⁺) (N : ℕ) → Prop l
  is-modulus-limit-prop-sequence-Metric-Space d N =
    Π-Prop
      ( ℕ)
      ( λ (n : ℕ) →
        hom-Prop (leq-ℕ-Prop N n) (neighbourhood-Metric-Space M d x (u n)))

  is-modulus-limit-sequence-Metric-Space : (d : ℚ⁺) (N : ℕ) → UU l
  is-modulus-limit-sequence-Metric-Space d N =
    type-Prop (is-modulus-limit-prop-sequence-Metric-Space d N)

  is-limit-sequence-Metric-Space : UU l
  is-limit-sequence-Metric-Space =
    (d : ℚ⁺) → Σ ℕ (is-modulus-limit-sequence-Metric-Space d)

  modulus-limit-sequence-Metric-Space :
    is-limit-sequence-Metric-Space → ℚ⁺ → ℕ
  modulus-limit-sequence-Metric-Space H d = pr1 (H d)

  is-modulus-modulus-limit-sequence-Metric-Space :
    (H : is-limit-sequence-Metric-Space) (d : ℚ⁺) →
    is-modulus-limit-sequence-Metric-Space
      ( d)
      ( modulus-limit-sequence-Metric-Space H d)
  is-modulus-modulus-limit-sequence-Metric-Space H d = pr2 (H d)
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
    tr
      ( λ d' → is-in-neighbourhood-Metric-Space M d' x y)
      ( left-diff-law-add-ℚ⁺ d₂ d (le-mediant-zero-ℚ⁺ d))
      ( is-triangular-neighbourhood-Metric-Space M
        ( x)
        ( u N)
        ( y)
        ( d₁)
        ( d₂)
        ( is-symmetric-neighbourhood-Metric-Space M d₂ y (u N) β)
        ( α))
    where
      d₂ : ℚ⁺
      d₂ = mediant-zero-ℚ⁺ d

      d₁ : ℚ⁺
      d₁ = le-diff-ℚ⁺ d₂ d (le-mediant-zero-ℚ⁺ d)

      Nx : ℕ
      Nx = modulus-limit-sequence-Metric-Space M u x H d₁

      Ny : ℕ
      Ny = modulus-limit-sequence-Metric-Space M u y K d₂

      N : ℕ
      N = max-ℕ Nx Ny

      α : is-in-neighbourhood-Metric-Space M d₁ x (u N)
      α =
        is-modulus-modulus-limit-sequence-Metric-Space M u x H d₁ N
          (leq-left-leq-max-ℕ N Nx Ny (refl-leq-ℕ N))

      β : is-in-neighbourhood-Metric-Space M d₂ y (u N)
      β =
        is-modulus-modulus-limit-sequence-Metric-Space M u y K d₂ N
          (leq-right-leq-max-ℕ N Nx Ny (refl-leq-ℕ N))
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
    (zero-ℕ , λ n H → is-reflexive-neighbourhood-Metric-Space M d x)
```
