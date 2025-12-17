# The large multiplicative group of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.large-multiplicative-group-of-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.large-abelian-groups
open import group-theory.large-groups
open import group-theory.large-monoids
open import group-theory.large-semigroups

open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.similarity-positive-real-numbers
```

</details>

## Idea

The [positive real numbers](real-numbers.positive-real-numbers.md) form a
[large abelian group](group-theory.large-abelian-groups.md) under
[multiplication](real-numbers.multiplication-positive-real-numbers.md).

## Definition

```agda
large-semigroup-mul-ℝ⁺ : Large-Semigroup lsuc
large-semigroup-mul-ℝ⁺ =
  make-Large-Semigroup
    ( ℝ⁺-Set)
    ( mul-ℝ⁺)
    ( associative-mul-ℝ⁺)

large-monoid-mul-ℝ⁺ : Large-Monoid lsuc (_⊔_)
large-monoid-mul-ℝ⁺ =
  make-Large-Monoid
    ( large-semigroup-mul-ℝ⁺)
    ( large-similarity-relation-sim-ℝ⁺)
    ( raise-ℝ⁺)
    ( λ l (x , _) → sim-raise-ℝ l x)
    ( preserves-sim-mul-ℝ⁺)
    ( one-ℝ⁺)
    ( left-unit-law-mul-ℝ⁺)
    ( right-unit-law-mul-ℝ⁺)

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
