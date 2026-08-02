# The large multiplicative monoid of nonnegative real numbers

```agda
module real-numbers.large-multiplicative-monoid-of-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.universe-levels

open import group-theory.large-commutative-monoids
open import group-theory.large-commutative-submonoids
open import group-theory.large-monoids
open import group-theory.large-semigroups
open import group-theory.large-submonoids
open import group-theory.large-subsemigroups

open import real-numbers.large-multiplicative-monoid-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.nonnegative-real-numbers
```

</details>

## Idea

The [nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) form a
[submonoid](group-theory.large-commutative-submonoids.md) of the
[large multiplicative monoid of real numbers](real-numbers.large-multiplicative-monoid-of-real-numbers.md).

## Definition

```agda
large-subsemigroup-mul-real-ℝ⁰⁺ :
  Large-Subsemigroup id large-semigroup-mul-ℝ
large-subsemigroup-mul-real-ℝ⁰⁺ =
  make-Large-Subsemigroup
    ( nonnegative-subset-cumulative-large-set-ℝ)
  ( λ _ _ → is-nonnegative-mul-ℝ)

large-submonoid-mul-real-ℝ⁰⁺ :
  Large-Submonoid id large-monoid-mul-ℝ
large-submonoid-mul-real-ℝ⁰⁺ =
  make-Large-Submonoid
    ( large-subsemigroup-mul-real-ℝ⁰⁺)
    ( is-nonnegative-one-ℝ)

large-commutative-submonoid-mul-real-ℝ⁰⁺ :
  Large-Commutative-Submonoid id large-commutative-monoid-mul-ℝ
large-commutative-submonoid-mul-real-ℝ⁰⁺ =
  make-Large-Commutative-Submonoid
    large-submonoid-mul-real-ℝ⁰⁺

large-semigroup-mul-ℝ⁰⁺ : Large-Semigroup lsuc (_⊔_)
large-semigroup-mul-ℝ⁰⁺ =
  large-semigroup-Large-Subsemigroup large-subsemigroup-mul-real-ℝ⁰⁺

large-monoid-mul-ℝ⁰⁺ : Large-Monoid lsuc (_⊔_)
large-monoid-mul-ℝ⁰⁺ =
  large-monoid-Large-Submonoid large-submonoid-mul-real-ℝ⁰⁺

large-commutative-monoid-mul-ℝ⁰⁺ : Large-Commutative-Monoid lsuc (_⊔_)
large-commutative-monoid-mul-ℝ⁰⁺ =
  large-commutative-monoid-Large-Commutative-Submonoid
    ( large-commutative-submonoid-mul-real-ℝ⁰⁺)
```
