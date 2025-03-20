# The multiplicative monoid of natural numbers

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory.multiplicative-monoid-of-natural-numbers
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers funext
open import elementary-number-theory.multiplication-natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.monoids funext
open import group-theory.semigroups funext
```

</details>

## Idea

The **multiplicative monoid of natural numbers** consists of
[natural numbers](elementary-number-theory.natural-numbers.md), and is equipped
with the
[multiplication operation](elementary-number-theory.multiplication-natural-numbers.md)
of the natural numbers as its multiplicative structure.

## Definitions

### The multiplicative semigroup of natural numbers

```agda
ℕ*-Semigroup : Semigroup lzero
pr1 ℕ*-Semigroup = ℕ-Set
pr1 (pr2 ℕ*-Semigroup) = mul-ℕ
pr2 (pr2 ℕ*-Semigroup) = associative-mul-ℕ
```

### The multiplicative monoid of natural numbers

```agda
ℕ*-Monoid : Monoid lzero
pr1 ℕ*-Monoid = ℕ*-Semigroup
pr1 (pr2 ℕ*-Monoid) = 1
pr1 (pr2 (pr2 ℕ*-Monoid)) = left-unit-law-mul-ℕ
pr2 (pr2 (pr2 ℕ*-Monoid)) = right-unit-law-mul-ℕ
```
