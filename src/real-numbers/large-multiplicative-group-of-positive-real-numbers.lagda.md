# The large multiplicative group of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.large-multiplicative-group-of-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.homomorphisms-large-commutative-monoids
open import group-theory.homomorphisms-large-monoids
open import group-theory.homomorphisms-large-semigroups
open import group-theory.large-abelian-groups
open import group-theory.large-commutative-monoids
open import group-theory.large-commutative-submonoids
open import group-theory.large-groups
open import group-theory.large-monoids
open import group-theory.large-semigroups
open import group-theory.large-submonoids
open import group-theory.large-subsemigroups

open import real-numbers.large-multiplicative-monoid-of-nonnegative-real-numbers
open import real-numbers.large-multiplicative-monoid-of-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
```

</details>

## Idea

The [positive real numbers](real-numbers.positive-real-numbers.md) form a
[large abelian group](group-theory.large-abelian-groups.md) under
[multiplication](real-numbers.multiplication-positive-real-numbers.md), which is
a [submonoid](group-theory.large-commutative-submonoids.md) of the
[large multiplicative monoid of real numbers](real-numbers.large-multiplicative-monoid-of-real-numbers.md).

## Definition

```agda
large-subsemigroup-mul-real-ℝ⁺ :
  Large-Subsemigroup id large-semigroup-mul-ℝ
large-subsemigroup-mul-real-ℝ⁺ =
  make-Large-Subsemigroup
    ( positive-subset-cumulative-large-set-ℝ)
    ( λ _ _ → is-positive-mul-ℝ)

large-submonoid-mul-real-ℝ⁺ :
  Large-Submonoid id large-monoid-mul-ℝ
large-submonoid-mul-real-ℝ⁺ =
  make-Large-Submonoid
    ( large-subsemigroup-mul-real-ℝ⁺)
    ( is-positive-one-ℝ)

large-commutative-submonoid-mul-real-ℝ⁺ :
  Large-Commutative-Submonoid id large-commutative-monoid-mul-ℝ
large-commutative-submonoid-mul-real-ℝ⁺ =
  make-Large-Commutative-Submonoid
    ( large-submonoid-mul-real-ℝ⁺)

large-semigroup-mul-ℝ⁺ : Large-Semigroup lsuc (_⊔_)
large-semigroup-mul-ℝ⁺ =
  large-semigroup-Large-Subsemigroup
    ( large-subsemigroup-mul-real-ℝ⁺)

large-monoid-mul-ℝ⁺ : Large-Monoid lsuc (_⊔_)
large-monoid-mul-ℝ⁺ =
  large-monoid-Large-Submonoid
    ( large-submonoid-mul-real-ℝ⁺)

large-commutative-monoid-mul-ℝ⁺ : Large-Commutative-Monoid lsuc (_⊔_)
large-commutative-monoid-mul-ℝ⁺ =
  large-commutative-monoid-Large-Commutative-Submonoid
    ( large-commutative-submonoid-mul-real-ℝ⁺)

large-group-mul-ℝ⁺ : Large-Group lsuc (_⊔_)
large-group-mul-ℝ⁺ =
  make-Large-Group
    ( large-monoid-mul-ℝ⁺)
    ( inv-ℝ⁺)
    ( preserves-sim-inv-ℝ⁺)
    ( eq-left-inverse-law-mul-ℝ⁺)
    ( eq-right-inverse-law-mul-ℝ⁺)

large-ab-mul-ℝ⁺ : Large-Ab lsuc (_⊔_)
large-ab-mul-ℝ⁺ =
  make-Large-Ab
    ( large-group-mul-ℝ⁺)
    ( commutative-mul-ℝ⁺)
```

## Properties

### The monoid homomorphism from the positive real numbers under multiplication to the nonnegative real numbers under multiplication

```agda
hom-large-semigroup-mul-nonnegative-ℝ⁺ :
  hom-Large-Semigroup
    ( large-semigroup-mul-ℝ⁺)
    ( large-semigroup-mul-ℝ⁰⁺)
hom-large-semigroup-mul-nonnegative-ℝ⁺ =
  make-hom-Large-Semigroup
    ( sim-preserving-map-nonnegative-ℝ⁺)
    ( eq-type-subtype is-nonnegative-prop-ℝ refl)

hom-large-monoid-mul-nonnegative-ℝ⁺ :
  hom-Large-Monoid
    ( large-monoid-mul-ℝ⁺)
    ( large-monoid-mul-ℝ⁰⁺)
hom-large-monoid-mul-nonnegative-ℝ⁺ =
  make-hom-Large-Monoid
    ( hom-large-semigroup-mul-nonnegative-ℝ⁺)
    ( eq-type-subtype is-nonnegative-prop-ℝ refl)

hom-large-commutative-monoid-mul-nonnnegative-ℝ⁺ :
  hom-Large-Commutative-Monoid
    ( large-commutative-monoid-mul-ℝ⁺)
    ( large-commutative-monoid-mul-ℝ⁰⁺)
hom-large-commutative-monoid-mul-nonnnegative-ℝ⁺ =
  make-hom-Large-Commutative-Monoid
    ( hom-large-monoid-mul-nonnegative-ℝ⁺)
```
