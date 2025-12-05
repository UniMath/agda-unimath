# Positive distributions on finite types

```agda
module finite-probability-theory.positive-distributions-on-finite-types where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.sums-of-finite-families-of-elements-commutative-rings

open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.large-rings
open import ring-theory.rings

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.large-ring-of-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A
{{#concept "positive distribution" Disambiguation="on a finite type" Agda=positive-distribution-Finite-Type}}
on a [finite type](univalent-combinatorics.finite-types.md) `Ω` is a function
into the [positive real numbers](real-numbers.positive-real-numbers.md),
`Pr : Ω → ℝ⁺`. We interpret the type `Ω` as the collection of _atomic events_,
and `Pr(x)` as the (unnormalized) _probability_ that the atomic event `x` will
occur. Note that for positive distributions no atomic event can be _impossible_
since `Pr(x)` is always strictly greater than `0`. The **total measure** of a
positive distribution `Pr` on a finite type `Ω` is the
[sum](group-theory.sums-of-finite-families-of-elements-abelian-groups.md)

$$
  ∑_{x ∈ Ω}\operatorname{Pr}(x).
$$

## Definitions

### Positive distributions on finite types

```agda
module _
  {l1 : Level} (l2 : Level) (Ω : Finite-Type l1)
  where

  positive-distribution-Finite-Type : UU (l1 ⊔ lsuc l2)
  positive-distribution-Finite-Type = type-Finite-Type Ω → ℝ⁺ l2

module _
  {l1 l2 : Level} (Ω : Finite-Type l1)
  (Pr : positive-distribution-Finite-Type l2 Ω)
  where

  real-positive-distribution-Finite-Type : type-Finite-Type Ω → ℝ l2
  real-positive-distribution-Finite-Type = real-ℝ⁺ ∘ Pr
```

### The total measure of a positive distribution on a finite type

```agda
module _
  {l1 l2 : Level} (Ω : Finite-Type l1)
  (Pr : positive-distribution-Finite-Type l2 Ω)
  where

  total-measure-positive-distribution-Finite-Type : ℝ l2
  total-measure-positive-distribution-Finite-Type =
    sum-finite-Commutative-Ring
      ( commutative-ring-ℝ l2)
      ( Ω)
      ( real-positive-distribution-Finite-Type Ω Pr)
```

## Properties

### The total measure of a positive distribution on an empty type is zero

```agda
module _
  {l1 l2 : Level} (Ω : Finite-Type l1)
  (Pr : positive-distribution-Finite-Type l2 Ω)
  where

  is-zero-total-measure-positive-distribution-is-empty-Finite-Type :
    is-empty (type-Finite-Type Ω) →
    total-measure-positive-distribution-Finite-Type Ω Pr ＝
    raise-zero-ℝ l2
  is-zero-total-measure-positive-distribution-is-empty-Finite-Type H =
    eq-zero-sum-finite-is-empty-Commutative-Ring
      ( commutative-ring-ℝ l2)
      ( Ω)
      ( H)
      ( real-positive-distribution-Finite-Type Ω Pr)
```
