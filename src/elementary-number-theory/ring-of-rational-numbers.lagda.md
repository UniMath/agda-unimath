# The ring of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.ring-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.group-of-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

The
[commutative group of rational numbers](elementary-number-theory.group-of-rational-numbers.md)
equipped with
[multiplication](elementary-number-theory.multiplication-rational-numbers.md) is
a [commutative](commutative-algebra.commutative-rings.md)
[ring](ring-theory.rings.md).

## Definitions

### The commutative ring of rational numbers

```agda
ℚ-Ring : Ring lzero
pr1 ℚ-Ring = ℚ-Ab
pr1 (pr1 (pr2 ℚ-Ring)) = mul-ℚ
pr2 (pr1 (pr2 ℚ-Ring)) = associative-mul-ℚ
pr1 (pr1 (pr2 (pr2 ℚ-Ring))) = one-ℚ
pr1 (pr2 (pr1 (pr2 (pr2 ℚ-Ring)))) = left-unit-law-mul-ℚ
pr2 (pr2 (pr1 (pr2 (pr2 ℚ-Ring)))) = right-unit-law-mul-ℚ
pr1 (pr2 (pr2 (pr2 ℚ-Ring))) = left-distributive-mul-add-ℚ
pr2 (pr2 (pr2 (pr2 ℚ-Ring))) = right-distributive-mul-add-ℚ

ℚ-Commutative-Ring : Commutative-Ring lzero
pr1 ℚ-Commutative-Ring = ℚ-Ring
pr2 ℚ-Commutative-Ring = commutative-mul-ℚ
```
