# The ring of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.ring-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.semigroups

open import ring-theory.rings
```

</details>

## Idea

The
[additive group of rational numbers](elementary-number-theory.additive-group-of-rational-numbers.md)
equipped with
[multiplication](elementary-number-theory.multiplication-rational-numbers.md) is
a commutative [division ring](ring-theory.division-rings.md).

## Definitions

### The compatible multiplicative structure on the abelian group of rational numbers

```agda
has-mul-ℚ-add-Ab : has-mul-Ab ℚ-add-Ab
pr1 has-mul-ℚ-add-Ab = has-associative-mul-Semigroup ℚ-mul-Semigroup
pr1 (pr2 has-mul-ℚ-add-Ab) = is-unital-mul-ℚ
pr1 (pr2 (pr2 has-mul-ℚ-add-Ab)) = left-distributive-mul-add-ℚ
pr2 (pr2 (pr2 has-mul-ℚ-add-Ab)) = right-distributive-mul-add-ℚ
```

### The ring of rational numbers

```agda
ℚ-Ring : Ring lzero
pr1 ℚ-Ring = ℚ-add-Ab
pr2 ℚ-Ring = has-mul-ℚ-add-Ab
```

## Properties

### The ring of rational numbers is commutative

```agda
ℚ-Commutative-Ring : Commutative-Ring lzero
pr1 ℚ-Commutative-Ring = ℚ-Ring
pr2 ℚ-Commutative-Ring = commutative-mul-ℚ
```
