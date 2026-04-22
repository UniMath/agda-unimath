# Sums of finite sequences of elements of vector spaces

```agda
module linear-algebra.sums-of-finite-sequences-of-elements-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.sums-of-finite-sequences-of-elements-left-modules-rings
open import linear-algebra.vector-spaces

open import lists.finite-sequences
```

</details>

## Idea

## Definition

```agda
sum-fin-sequence-type-Vector-Space :
  {l1 l2 : Level} (K : Heyting-Field l1) (V : Vector-Space l2 K) →
  (n : ℕ) → fin-sequence (type-Vector-Space K V) n → type-Vector-Space K V
sum-fin-sequence-type-Vector-Space K V =
  sum-fin-sequence-type-left-module-Ring (ring-Heyting-Field K) V
```
