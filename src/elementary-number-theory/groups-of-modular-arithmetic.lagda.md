# The groups `ℤ/kℤ`

```agda
module elementary-number-theory.groups-of-modular-arithmetic where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups
```

</details>

## Idea

The integers modulo k, equipped with the zero-element, addition, and negatives,
form groups.

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

ℤ-Mod-Ab : (k : ℕ) → Ab lzero
pr1 (ℤ-Mod-Ab k) = ℤ-Mod-Group k
pr2 (ℤ-Mod-Ab k) = commutative-add-ℤ-Mod k
```
