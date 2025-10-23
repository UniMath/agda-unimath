# The group of integers

```agda
module elementary-number-theory.group-of-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups
```

</details>

## Idea

The type of [integers](elementary-number-theory.integers.md), equipped with
zero, [addition](elementary-number-theory.addition-integers.md), and negation,
forms a [group](group-theory.groups.md).

## Definition

```agda
ℤ-Semigroup : Semigroup lzero
pr1 ℤ-Semigroup = ℤ-Set
pr1 (pr2 ℤ-Semigroup) = add-ℤ
pr2 (pr2 ℤ-Semigroup) = associative-add-ℤ

ℤ-Group : Group lzero
pr1 ℤ-Group = ℤ-Semigroup
pr1 (pr1 (pr2 ℤ-Group)) = zero-ℤ
pr1 (pr2 (pr1 (pr2 ℤ-Group))) = left-unit-law-add-ℤ
pr2 (pr2 (pr1 (pr2 ℤ-Group))) = right-unit-law-add-ℤ
pr1 (pr2 (pr2 ℤ-Group)) = neg-ℤ
pr1 (pr2 (pr2 (pr2 ℤ-Group))) = left-inverse-law-add-ℤ
pr2 (pr2 (pr2 (pr2 ℤ-Group))) = right-inverse-law-add-ℤ

ℤ-Ab : Ab lzero
pr1 ℤ-Ab = ℤ-Group
pr2 ℤ-Ab = commutative-add-ℤ
```
