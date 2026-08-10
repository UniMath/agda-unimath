# Sums of finite sequences of elements in left modules over commutative rings

```agda
module linear-algebra.sums-of-finite-sequences-of-elements-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import linear-algebra.left-modules-commutative-rings

open import lists.finite-sequences
```

</details>

## Idea

The
{{#concept "sum" Disambiguation="of elements of left modules over commutative rings" Agda=sum-fin-sequence-type-left-module-Commutative-Ring}}
operation on [left modules](linear-algebra.left-modules-commutative-rings.md)
over [commutative rings](commutative-algebra.commutative-rings.md) generalizes
its binary addition operation to any
[finite sequence](lists.finite-sequences.md) of elements of the module.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  where

  sum-fin-sequence-type-left-module-Commutative-Ring :
    (n : ℕ) →
    fin-sequence (type-left-module-Commutative-Ring R M) n →
    type-left-module-Commutative-Ring R M
  sum-fin-sequence-type-left-module-Commutative-Ring =
    sum-fin-sequence-type-Ab (ab-left-module-Commutative-Ring R M)
```
