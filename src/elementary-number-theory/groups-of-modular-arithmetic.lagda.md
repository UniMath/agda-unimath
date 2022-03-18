# The groups ℤ/kℤ

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.groups-of-modular-arithmetic where

open import elementary-number-theory.modular-arithmetic using
  ( ℤ-Mod-Set; add-ℤ-Mod; associative-add-ℤ-Mod; zero-ℤ-Mod; neg-ℤ-Mod;
    left-unit-law-add-ℤ-Mod; right-unit-law-add-ℤ-Mod;
    left-inverse-law-add-ℤ-Mod; right-inverse-law-add-ℤ-Mod)
open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.universe-levels using (lzero)

open import group-theory.abstract-groups using (Group)
open import group-theory.semigroups using (Semigroup)
```

## Idea

The integers modulo k, equipped with the zero-element, addition, and negatives, form groups.

## Definition

```agda
ℤ-Mod-Semigroup : (k : ℕ) → Semigroup lzero
pr1 (ℤ-Mod-Semigroup k) = ℤ-Mod-Set k
pr1 (pr2 (ℤ-Mod-Semigroup k)) = add-ℤ-Mod k
pr2 (pr2 (ℤ-Mod-Semigroup k)) = associative-add-ℤ-Mod k

ℤ-Mod-Group : (k : ℕ) → Group lzero
pr1 (ℤ-Mod-Group k) = ℤ-Mod-Semigroup k
pr1 (pr1 (pr2 (ℤ-Mod-Group k))) = zero-ℤ-Mod k
pr1 (pr2 (pr1 (pr2 (ℤ-Mod-Group k)))) = left-unit-law-add-ℤ-Mod k
pr2 (pr2 (pr1 (pr2 (ℤ-Mod-Group k)))) = right-unit-law-add-ℤ-Mod k
pr1 (pr2 (pr2 (ℤ-Mod-Group k))) = neg-ℤ-Mod k
pr1 (pr2 (pr2 (pr2 (ℤ-Mod-Group k)))) = left-inverse-law-add-ℤ-Mod k
pr2 (pr2 (pr2 (pr2 (ℤ-Mod-Group k)))) = right-inverse-law-add-ℤ-Mod k
```
