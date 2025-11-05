# The large multiplicative monoid of Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.large-multiplicative-monoid-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.large-abelian-groups
open import group-theory.large-commutative-monoids
open import group-theory.large-monoids
open import group-theory.large-semigroups

open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) form a
[large commutative mopnoid](group-theory.large-commutative-monoids.md) under
[multiplication](real-numbers.multiplication-real-numbers.md).

## Definition

```agda
large-semigroup-mul-ℝ : Large-Semigroup lsuc
large-semigroup-mul-ℝ =
  make-Large-Semigroup
    ( ℝ-Set)
    ( mul-ℝ)
    ( associative-mul-ℝ)

large-monoid-mul-ℝ : Large-Monoid lsuc _⊔_
large-monoid-mul-ℝ =
  make-Large-Monoid
    ( large-semigroup-mul-ℝ)
    ( large-similarity-relation-sim-ℝ)
    ( raise-ℝ)
    ( sim-raise-ℝ)
    ( preserves-sim-mul-ℝ)
    ( one-ℝ)
    ( left-unit-law-mul-ℝ)
    ( right-unit-law-mul-ℝ)

large-commutative-monoid-mul-ℝ : Large-Commutative-Monoid lsuc _⊔_
large-commutative-monoid-mul-ℝ =
  make-Large-Commutative-Monoid
    ( large-monoid-mul-ℝ)
    ( commutative-mul-ℝ)
```

## Properties

### The small commutative monoid of real numbers at a universe level

```agda
commutative-monoid-mul-ℝ : (l : Level) → Commutative-Monoid (lsuc l)
commutative-monoid-mul-ℝ =
  commutative-monoid-Large-Commutative-Monoid large-commutative-monoid-mul-ℝ
```
