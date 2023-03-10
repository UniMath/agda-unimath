# The commutative semiring of natural numbers

```agda
module elementary-number-theory.commutative-semiring-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import ring-theory.semirings
```

</details>

## Definition

### The commutative semiring of natural numbers

```agda
ℕ-Commutative-Monoid : Commutative-Monoid lzero
pr1 ℕ-Commutative-Monoid = ℕ-Monoid
pr2 ℕ-Commutative-Monoid = commutative-add-ℕ

has-mul-ℕ-Commutative-Monoid :
  has-mul-Commutative-Monoid ℕ-Commutative-Monoid
pr1 (pr1 has-mul-ℕ-Commutative-Monoid) = mul-ℕ
pr2 (pr1 has-mul-ℕ-Commutative-Monoid) = associative-mul-ℕ
pr1 (pr1 (pr2 has-mul-ℕ-Commutative-Monoid)) = 1
pr1 (pr2 (pr1 (pr2 has-mul-ℕ-Commutative-Monoid))) = left-unit-law-mul-ℕ
pr2 (pr2 (pr1 (pr2 has-mul-ℕ-Commutative-Monoid))) = right-unit-law-mul-ℕ
pr1 (pr2 (pr2 has-mul-ℕ-Commutative-Monoid)) = left-distributive-mul-add-ℕ
pr2 (pr2 (pr2 has-mul-ℕ-Commutative-Monoid)) = right-distributive-mul-add-ℕ

ℕ-Semiring : Semiring lzero
pr1 ℕ-Semiring = ℕ-Commutative-Monoid
pr1 (pr2 ℕ-Semiring) = has-mul-ℕ-Commutative-Monoid
pr1 (pr2 (pr2 ℕ-Semiring)) = left-zero-law-mul-ℕ
pr2 (pr2 (pr2 ℕ-Semiring)) = right-zero-law-mul-ℕ

ℕ-Commutative-Semiring : Commutative-Semiring lzero
pr1 ℕ-Commutative-Semiring = ℕ-Semiring
pr2 ℕ-Commutative-Semiring = commutative-mul-ℕ
```
