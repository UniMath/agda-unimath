# The additive group of rational numbers

```agda
module elementary-number-theory.group-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups
```

</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
equipped with [addition](elementary-number-theory.addition-rational-numbers.md)
is a [commutative](group-theory.abelian-groups.md)
[group](group-theory.groups.md) with unit `zero-ℚ` and inverse given by`neg-ℚ`.

## Definitions

### The additive abelian group of rational numbers

```agda
ℚ-Semigroup : Semigroup lzero
pr1 ℚ-Semigroup = ℚ-Set
pr1 (pr2 ℚ-Semigroup) = add-ℚ
pr2 (pr2 ℚ-Semigroup) = associative-add-ℚ

ℚ-Group : Group lzero
pr1 ℚ-Group = ℚ-Semigroup
pr1 (pr1 (pr2 ℚ-Group)) = zero-ℚ
pr1 (pr2 (pr1 (pr2 ℚ-Group))) = left-unit-law-add-ℚ
pr2 (pr2 (pr1 (pr2 ℚ-Group))) = right-unit-law-add-ℚ
pr1 (pr2 (pr2 ℚ-Group)) = neg-ℚ
pr1 (pr2 (pr2 (pr2 ℚ-Group))) = left-inverse-law-add-ℚ
pr2 (pr2 (pr2 (pr2 ℚ-Group))) = right-inverse-law-add-ℚ

ℚ-Ab : Ab lzero
pr1 ℚ-Ab = ℚ-Group
pr2 ℚ-Ab = commutative-add-ℚ
```
