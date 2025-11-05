# The large additive group of Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.large-additive-group-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.large-abelian-groups
open import group-theory.large-commutative-monoids
open import group-theory.large-groups
open import group-theory.large-monoids
open import group-theory.large-semigroups

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) form a
[large abelian group](group-theory.large-abelian-groups.md) under
[addition](real-numbers.addition-real-numbers.md).

## Definition

```agda
large-semigroup-add-ℝ : Large-Semigroup lsuc
large-semigroup-add-ℝ =
  make-Large-Semigroup
    ( ℝ-Set)
    ( add-ℝ)
    ( associative-add-ℝ)

large-monoid-add-ℝ : Large-Monoid lsuc _⊔_
large-monoid-add-ℝ =
  make-Large-Monoid
    ( large-semigroup-add-ℝ)
    ( large-similarity-relation-sim-ℝ)
    ( raise-ℝ)
    ( sim-raise-ℝ)
    ( λ a b a~b c d c~d → preserves-sim-add-ℝ a~b c~d)
    ( zero-ℝ)
    ( left-unit-law-add-ℝ)
    ( right-unit-law-add-ℝ)

large-commutative-monoid-add-ℝ : Large-Commutative-Monoid lsuc _⊔_
large-commutative-monoid-add-ℝ =
  make-Large-Commutative-Monoid
    ( large-monoid-add-ℝ)
    ( commutative-add-ℝ)

large-group-add-ℝ : Large-Group lsuc _⊔_
large-group-add-ℝ =
  make-Large-Group
    ( large-monoid-add-ℝ)
    ( neg-ℝ)
    ( λ _ _ → preserves-sim-neg-ℝ)
    ( eq-left-inverse-law-add-ℝ)
    ( eq-right-inverse-law-add-ℝ)

large-ab-add-ℝ : Large-Ab lsuc _⊔_
large-ab-add-ℝ =
  make-Large-Ab
    ( large-group-add-ℝ)
    ( commutative-add-ℝ)
```

## Properties

### The small abelian group of real numbers at a universe level

```agda
ab-add-ℝ : (l : Level) → Ab (lsuc l)
ab-add-ℝ = ab-Large-Ab large-ab-add-ℝ
```
