# Measures on finite types

```agda
module finite-probability-theory.measures-on-finite-types where
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
{{#concept "measure" Disambiguation="on a finite type" Agda=measure-Finite-Type}}
on a [finite type](univalent-combinatorics.finite-types.md) is a function into
the [positive real numbers](real-numbers.positive-real-numbers.md).

THe **total measure** of a measure `μ` on a finite type `Ω` is the
[sum](group-theory.sums-of-finite-families-of-elements-abelian-groups.md)

\[ ∑\_{x ∈ Ω} μ(x). \]

## Definition

### Measures on finite types

```agda
module _
  {l : Level} (Ω : Finite-Type l)
  where

  measure-Finite-Type : UU (lsuc lzero ⊔ l)
  measure-Finite-Type = type-Finite-Type Ω → ℝ⁺ lzero

  real-measure-Finite-Type :
    measure-Finite-Type → type-Finite-Type Ω → ℝ lzero
  real-measure-Finite-Type μ = real-ℝ⁺ ∘ μ

  total-measure-Finite-Type : measure-Finite-Type → ℝ lzero
  total-measure-Finite-Type μ =
    sum-finite-Ab
      ( abelian-group-add-ℝ-lzero)
      ( Ω)
      ( real-ℝ⁺ ∘ μ)
```

## Properties

### The total measure of an empty type is zero

```agda
module _
  {l : Level} (Ω : Finite-Type l) (μ : measure-Finite-Type Ω)
  where

  is-zero-total-measure-is-empty-Finite-Type :
    is-empty (type-Finite-Type Ω) →
    total-measure-Finite-Type Ω μ ＝ zero-ℝ
  is-zero-total-measure-is-empty-Finite-Type H =
    eq-zero-sum-finite-is-empty-Ab
      ( abelian-group-add-ℝ-lzero)
      ( Ω)
      ( H)
      ( real-ℝ⁺ ∘ μ)
```
