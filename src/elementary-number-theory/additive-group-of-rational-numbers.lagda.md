# The additive group of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.additive-group-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
equipped with [addition](elementary-number-theory.addition-rational-numbers.md)
is a [commutative group](group-theory.abelian-groups.md) with unit `zero-ℚ` and
inverse given by`neg-ℚ`.

## Definitions

### The additive abelian group of rational numbers

```agda
ℚ-add-Semigroup : Semigroup lzero
pr1 ℚ-add-Semigroup = ℚ-Set
pr1 (pr2 ℚ-add-Semigroup) = add-ℚ
pr2 (pr2 ℚ-add-Semigroup) = associative-add-ℚ

is-unital-add-ℚ : is-unital add-ℚ
pr1 is-unital-add-ℚ = zero-ℚ
pr1 (pr2 is-unital-add-ℚ) = left-unit-law-add-ℚ
pr2 (pr2 is-unital-add-ℚ) = right-unit-law-add-ℚ

ℚ-add-Monoid : Monoid lzero
pr1 ℚ-add-Monoid = ℚ-add-Semigroup
pr2 ℚ-add-Monoid = is-unital-add-ℚ

ℚ-add-Group : Group lzero
pr1 ℚ-add-Group = ℚ-add-Semigroup
pr1 (pr2 ℚ-add-Group) = is-unital-add-ℚ
pr1 (pr2 (pr2 ℚ-add-Group)) = neg-ℚ
pr1 (pr2 (pr2 (pr2 ℚ-add-Group))) = left-inverse-law-add-ℚ
pr2 (pr2 (pr2 (pr2 ℚ-add-Group))) = right-inverse-law-add-ℚ
```

## Properties

### Tha additive group of rational numbers is commutative

```agda
ℚ-add-Ab : Ab lzero
pr1 ℚ-add-Ab = ℚ-add-Group
pr2 ℚ-add-Ab = commutative-add-ℚ
```
