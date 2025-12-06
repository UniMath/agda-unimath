# Power series centered at zero in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.power-series-at-zero-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.absolute-convergence-series-real-numbers
open import analysis.convergent-series-real-numbers
open import analysis.series-real-numbers

open import commutative-algebra.formal-power-series-commutative-rings

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.partial-functions
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.large-ring-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.powers-real-numbers
```

</details>

## Idea

A
{{#concept "power series centered at zero" Agda=power-series-at-zero-ℝ Disambiguation="in the real numbers"}}
is a
[power series](commutative-algebra.formal-power-series-commutative-rings.md) in
the
[commutative ring of real numbers](real-numbers.large-ring-of-real-numbers.md)
with [convergence](analysis.convergent-series-real-numbers.md) considered with
respect to the
[standard metric space on the real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
power-series-at-zero-ℝ : (l : Level) → UU (lsuc l)
power-series-at-zero-ℝ l =
  formal-power-series-Commutative-Ring (commutative-ring-ℝ l)

coefficient-power-series-at-zero-ℝ :
  {l : Level} → power-series-at-zero-ℝ l → sequence (ℝ l)
coefficient-power-series-at-zero-ℝ {l} =
  coefficient-formal-power-series-Commutative-Ring (commutative-ring-ℝ l)

power-series-at-zero-coefficients-ℝ :
  {l : Level} → sequence (ℝ l) → power-series-at-zero-ℝ l
power-series-at-zero-coefficients-ℝ {l} =
  formal-power-series-coefficients-Commutative-Ring (commutative-ring-ℝ l)
```

## Properties

### The series resulting from evaluating a power series at a point

```agda
term-at-point-power-series-at-zero-ℝ :
  {l : Level} → power-series-at-zero-ℝ l → ℝ l → sequence (ℝ l)
term-at-point-power-series-at-zero-ℝ σ x n =
  coefficient-power-series-at-zero-ℝ σ n *ℝ power-ℝ n x

compute-series-at-point-power-series-at-zero-ℝ :
  {l : Level} → power-series-at-zero-ℝ l → ℝ l → series-ℝ l
compute-series-at-point-power-series-at-zero-ℝ σ x =
  series-terms-ℝ (term-at-point-power-series-at-zero-ℝ σ x)
```

### Convergence of a power series at a point

```agda
is-convergent-at-point-prop-power-series-at-zero-ℝ :
  {l : Level} → power-series-at-zero-ℝ l → ℝ l → Prop (lsuc l)
is-convergent-at-point-prop-power-series-at-zero-ℝ σ x =
  is-convergent-prop-series-ℝ
    ( compute-series-at-point-power-series-at-zero-ℝ σ x)

is-convergent-at-point-power-series-at-zero-ℝ :
  {l : Level} → power-series-at-zero-ℝ l → ℝ l → UU (lsuc l)
is-convergent-at-point-power-series-at-zero-ℝ σ x =
  type-Prop (is-convergent-at-point-prop-power-series-at-zero-ℝ σ x)
```

### Absolute convergence of a power series at a point

```agda
is-absolutely-convergent-at-point-prop-power-series-at-zero-ℝ :
  {l : Level} → power-series-at-zero-ℝ l → ℝ l → Prop (lsuc l)
is-absolutely-convergent-at-point-prop-power-series-at-zero-ℝ σ x =
  is-absolutely-convergent-prop-series-ℝ
    ( compute-series-at-point-power-series-at-zero-ℝ σ x)

is-absolutely-convergent-at-point-power-series-at-zero-ℝ :
  {l : Level} → power-series-at-zero-ℝ l → ℝ l → UU (lsuc l)
is-absolutely-convergent-at-point-power-series-at-zero-ℝ σ x =
  type-Prop (is-absolutely-convergent-at-point-prop-power-series-at-zero-ℝ σ x)
```

### Convergence of a power series everywhere

```agda
is-convergent-everywhere-prop-power-series-at-zero-ℝ :
  {l : Level} → power-series-at-zero-ℝ l → Prop (lsuc l)
is-convergent-everywhere-prop-power-series-at-zero-ℝ {l} σ =
  Π-Prop (ℝ l) (is-convergent-at-point-prop-power-series-at-zero-ℝ σ)

is-convergent-everywhere-power-series-at-zero-ℝ :
  {l : Level} → power-series-at-zero-ℝ l → UU (lsuc l)
is-convergent-everywhere-power-series-at-zero-ℝ σ =
  type-Prop (is-convergent-everywhere-prop-power-series-at-zero-ℝ σ)

convergent-everywhere-power-series-at-zero-ℝ : (l : Level) → UU (lsuc l)
convergent-everywhere-power-series-at-zero-ℝ l =
  type-subtype (is-convergent-everywhere-prop-power-series-at-zero-ℝ {l})

ev-convergent-everywhere-power-series-at-zero-ℝ :
  {l : Level} → convergent-everywhere-power-series-at-zero-ℝ l → ℝ l → ℝ l
ev-convergent-everywhere-power-series-at-zero-ℝ (σ , H) x =
  sum-convergent-series-ℝ
    ( compute-series-at-point-power-series-at-zero-ℝ σ x , H x)
```

### The partial function of evaluating a power series

```agda
partial-ev-power-series-at-zero-ℝ :
  {l : Level} → power-series-at-zero-ℝ l → partial-function (lsuc l) (ℝ l) (ℝ l)
partial-ev-power-series-at-zero-ℝ σ x =
  ( is-convergent-at-point-prop-power-series-at-zero-ℝ σ x , pr1)
```
