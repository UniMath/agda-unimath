# The additive group of Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.additive-group-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The [real numbers](real-numbers.dedekind-real-numbers.md) form an
[abelian group](group-theory.abelian-groups.md) under
[addition](real-numbers.addition-real-numbers.md).

## Definition

```agda
semigroup-add-ℝ-lzero : Semigroup (lsuc lzero)
semigroup-add-ℝ-lzero =
  ( ℝ-Set lzero ,
    add-ℝ ,
    associative-add-ℝ)

monoid-add-ℝ-lzero : Monoid (lsuc lzero)
monoid-add-ℝ-lzero =
  ( semigroup-add-ℝ-lzero ,
    zero-ℝ ,
    left-unit-law-add-ℝ ,
    right-unit-law-add-ℝ)

commutative-monoid-add-ℝ-lzero : Commutative-Monoid (lsuc lzero)
commutative-monoid-add-ℝ-lzero =
  ( monoid-add-ℝ-lzero ,
    commutative-add-ℝ)

group-add-ℝ-lzero : Group (lsuc lzero)
group-add-ℝ-lzero =
  ( ( semigroup-add-ℝ-lzero) ,
    ( zero-ℝ , left-unit-law-add-ℝ , right-unit-law-add-ℝ) ,
    ( neg-ℝ ,
      eq-sim-ℝ ∘ left-inverse-law-add-ℝ ,
      eq-sim-ℝ ∘ right-inverse-law-add-ℝ))

ab-add-ℝ-lzero : Ab (lsuc lzero)
ab-add-ℝ-lzero =
  ( group-add-ℝ-lzero ,
    commutative-add-ℝ)
```
