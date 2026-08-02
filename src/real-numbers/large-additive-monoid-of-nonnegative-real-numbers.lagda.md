# The large additive monoid of nonnegative real numbers

```agda
module real-numbers.large-additive-monoid-of-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import group-theory.large-commutative-monoids
open import group-theory.large-commutative-submonoids
open import group-theory.large-monoids
open import group-theory.large-semigroups
open import group-theory.large-submonoids
open import group-theory.large-subsemigroups

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.large-additive-group-of-real-numbers
open import real-numbers.nonnegative-real-numbers
```

</details>

## Idea

The [nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) form a
[submonoid](group-theory.large-commutative-submonoids.md) of the
[large additive monoid of real numbers](real-numbers.large-additive-group-of-real-numbers.md).

## Definition

```agda
large-subsemigroup-add-real-ℝ⁰⁺ :
  Large-Subsemigroup id large-semigroup-add-ℝ
large-subsemigroup-add-real-ℝ⁰⁺ =
  make-Large-Subsemigroup
    ( nonnegative-subset-cumulative-large-set-ℝ)
    ( λ x y 0≤x 0≤y → is-nonnegative-real-add-ℝ⁰⁺ (x , 0≤x) (y , 0≤y))

large-submonoid-add-real-ℝ⁰⁺ :
  Large-Submonoid id large-monoid-add-ℝ
large-submonoid-add-real-ℝ⁰⁺ =
  make-Large-Submonoid
    ( large-subsemigroup-add-real-ℝ⁰⁺)
    ( is-nonnegative-zero-ℝ)

large-commutative-submonoid-add-real-ℝ⁰⁺ :
  Large-Commutative-Submonoid id large-commutative-monoid-add-ℝ
large-commutative-submonoid-add-real-ℝ⁰⁺ =
  make-Large-Commutative-Submonoid
    ( large-submonoid-add-real-ℝ⁰⁺)

large-semigroup-add-ℝ⁰⁺ :
  Large-Semigroup lsuc (_⊔_)
large-semigroup-add-ℝ⁰⁺ =
  large-semigroup-Large-Subsemigroup large-subsemigroup-add-real-ℝ⁰⁺

large-monoid-add-ℝ⁰⁺ :
  Large-Monoid lsuc (_⊔_)
large-monoid-add-ℝ⁰⁺ =
  large-monoid-Large-Submonoid large-submonoid-add-real-ℝ⁰⁺

large-commutative-monoid-add-ℝ⁰⁺ :
  Large-Commutative-Monoid lsuc (_⊔_)
large-commutative-monoid-add-ℝ⁰⁺ =
  large-commutative-monoid-Large-Commutative-Submonoid
    ( large-commutative-submonoid-add-real-ℝ⁰⁺)
```
