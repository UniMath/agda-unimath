# Positive distributions on finite types

```agda
module finite-probability-theory.positive-distributions-on-finite-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.sums-of-finite-families-of-elements-abelian-groups

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A
{{#concept "positive distribution" Disambiguation="on a finite type" Agda=positive-distribution-Finite-Type}}
on a [finite type](univalent-combinatorics.finite-types.md) is a function into
the [positive real numbers](real-numbers.positive-real-numbers.md).

The **total measure** of a positive-distribution `μ` on a finite type `Ω` is the
[sum](group-theory.sums-of-finite-families-of-elements-abelian-groups.md)

$$
  ∑_{x ∈ Ω} μ(x).
$$

## Definitions

### Positive distributions on finite types

```agda
module _
  {l : Level} (Ω : Finite-Type l)
  where

  positive-distribution-Finite-Type : UU (lsuc lzero ⊔ l)
  positive-distribution-Finite-Type = type-Finite-Type Ω → ℝ⁺ lzero

  real-positive-distribution-Finite-Type :
    positive-distribution-Finite-Type → type-Finite-Type Ω → ℝ lzero
  real-positive-distribution-Finite-Type μ = real-ℝ⁺ ∘ μ
```

### The total measure of a positive distribution on a finite type

```agda
module _
  {l : Level} (Ω : Finite-Type l)
  (μ : positive-distribution-Finite-Type Ω)
  where

  total-measure-positive-distribution-Finite-Type : ℝ lzero
  total-measure-positive-distribution-Finite-Type =
    sum-finite-Ab
      ( abelian-group-add-ℝ-lzero)
      ( Ω)
      ( real-positive-distribution-Finite-Type Ω μ)
```

## Properties

### The total measure of a positive distribution on an empty type is zero

```agda
module _
  {l : Level} (Ω : Finite-Type l) (μ : positive-distribution-Finite-Type Ω)
  where

  is-zero-total-measure-positive-distribution-is-empty-Finite-Type :
    is-empty (type-Finite-Type Ω) →
    total-measure-positive-distribution-Finite-Type Ω μ ＝ zero-ℝ
  is-zero-total-measure-positive-distribution-is-empty-Finite-Type H =
    eq-zero-sum-finite-is-empty-Ab
      ( abelian-group-add-ℝ-lzero)
      ( Ω)
      ( H)
      ( real-positive-distribution-Finite-Type Ω μ)
```
