# The commutative ring of integers

```agda
module elementary-number-theory.commutative-ring-of-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups

open import ring-theory.rings
```

</details>

## Definition

```agda
ℤ-Ab : Ab lzero
pr1 ℤ-Ab = ℤ-Group
pr2 ℤ-Ab = commutative-add-ℤ

ℤ-Ring : Ring lzero
pr1 ℤ-Ring = ℤ-Ab
pr1 (pr1 (pr2 ℤ-Ring)) = mul-ℤ
pr2 (pr1 (pr2 ℤ-Ring)) = associative-mul-ℤ
pr1 (pr1 (pr2 (pr2 ℤ-Ring))) = one-ℤ
pr1 (pr2 (pr1 (pr2 (pr2 ℤ-Ring)))) = left-unit-law-mul-ℤ
pr2 (pr2 (pr1 (pr2 (pr2 ℤ-Ring)))) = right-unit-law-mul-ℤ
pr1 (pr2 (pr2 (pr2 ℤ-Ring))) = left-distributive-mul-add-ℤ
pr2 (pr2 (pr2 (pr2 ℤ-Ring))) = right-distributive-mul-add-ℤ

ℤ-Commutative-Ring : Commutative-Ring lzero
pr1 ℤ-Commutative-Ring = ℤ-Ring
pr2 ℤ-Commutative-Ring = commutative-mul-ℤ
```
