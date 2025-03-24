# The monoid of natural numbers with addition

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.monoid-of-natural-numbers-with-addition
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.commutative-monoids funext univalence truncations
open import group-theory.monoids funext univalence truncations
open import group-theory.semigroups funext univalence
```

</details>

## Idea

The natural numbers equipped with `0` and addition is a commutative monoid.

## Definitions

### The Semigroup of natural numbers

```agda
ℕ-Semigroup : Semigroup lzero
pr1 ℕ-Semigroup = ℕ-Set
pr1 (pr2 ℕ-Semigroup) = add-ℕ
pr2 (pr2 ℕ-Semigroup) = associative-add-ℕ
```

### The monoid of natural numbers

```agda
ℕ-Monoid : Monoid lzero
pr1 ℕ-Monoid = ℕ-Semigroup
pr1 (pr2 ℕ-Monoid) = 0
pr1 (pr2 (pr2 ℕ-Monoid)) = left-unit-law-add-ℕ
pr2 (pr2 (pr2 ℕ-Monoid)) = right-unit-law-add-ℕ
```

### The commutative monoid of natural numbers

```agda
ℕ-Commutative-Monoid : Commutative-Monoid lzero
pr1 ℕ-Commutative-Monoid = ℕ-Monoid
pr2 ℕ-Commutative-Monoid = commutative-add-ℕ
```
