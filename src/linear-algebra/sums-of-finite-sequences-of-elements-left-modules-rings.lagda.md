# Sums of finite sequences of elements of left modules over rings

```agda
module linear-algebra.sums-of-finite-sequences-of-elements-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import linear-algebra.left-modules-rings

open import lists.finite-sequences

open import ring-theory.rings
```

</details>

## Idea

## Definition

```agda
sum-fin-sequence-type-left-module-Ring :
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R) →
  (n : ℕ) → fin-sequence (type-left-module-Ring R M) n →
  type-left-module-Ring R M
sum-fin-sequence-type-left-module-Ring R M =
  sum-fin-sequence-type-Ab (ab-left-module-Ring R M)
```
