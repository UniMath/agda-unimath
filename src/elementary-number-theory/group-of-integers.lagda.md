# The group of integers

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.group-of-integers where

open import elementary-number-theory.addition-integers using
  ( add-ℤ; associative-add-ℤ; left-unit-law-add-ℤ; right-unit-law-add-ℤ;
    left-inverse-law-add-ℤ; right-inverse-law-add-ℤ)
open import elementary-number-theory.equality-integers using (ℤ-Set)
open import elementary-number-theory.integers using (zero-ℤ; neg-ℤ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.universe-levels using (lzero)

open import group-theory.groups using (Group)
open import group-theory.semigroups using (Semigroup)
```

## Idea

The type of integers, equipped with a zero-element, addition, and negatives, forms a group.

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
```
