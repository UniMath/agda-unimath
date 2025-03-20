# The ring of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

open import foundation.function-extensionality-axiom

module
  elementary-number-theory.ring-of-rational-numbers
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings funext

open import elementary-number-theory.additive-group-of-rational-numbers funext
open import elementary-number-theory.multiplication-rational-numbers funext
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers funext

open import foundation.coproduct-types funext
open import foundation.dependent-pair-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.semigroups funext

open import ring-theory.rings funext
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
has-mul-abelian-group-add-ℚ : has-mul-Ab abelian-group-add-ℚ
pr1 has-mul-abelian-group-add-ℚ = has-associative-mul-Semigroup semigroup-mul-ℚ
pr1 (pr2 has-mul-abelian-group-add-ℚ) = is-unital-mul-ℚ
pr1 (pr2 (pr2 has-mul-abelian-group-add-ℚ)) = left-distributive-mul-add-ℚ
pr2 (pr2 (pr2 has-mul-abelian-group-add-ℚ)) = right-distributive-mul-add-ℚ
```

### The ring of rational numbers

```agda
ring-ℚ : Ring lzero
pr1 ring-ℚ = abelian-group-add-ℚ
pr2 ring-ℚ = has-mul-abelian-group-add-ℚ
```

## Properties

### The ring of rational numbers is commutative

```agda
commutative-ring-ℚ : Commutative-Ring lzero
pr1 commutative-ring-ℚ = ring-ℚ
pr2 commutative-ring-ℚ = commutative-mul-ℚ
```
