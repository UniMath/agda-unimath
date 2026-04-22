# Sums of finite sequences of elements of real vector spaces

```agda
module linear-algebra.sums-of-finite-sequences-of-elements-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.real-vector-spaces
open import linear-algebra.sums-of-finite-sequences-of-elements-vector-spaces

open import lists.finite-sequences

open import real-numbers.field-of-real-numbers
```

</details>

## Idea

## Definition

```agda
sum-fin-sequence-type-ℝ-Vector-Space :
  {l1 l2 : Level} (V : ℝ-Vector-Space l1 l2) →
  (n : ℕ) → fin-sequence (type-ℝ-Vector-Space V) n → type-ℝ-Vector-Space V
sum-fin-sequence-type-ℝ-Vector-Space =
  sum-fin-sequence-type-Vector-Space (heyting-field-ℝ _)
```
