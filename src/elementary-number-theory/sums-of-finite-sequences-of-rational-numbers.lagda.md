# Sums of finite sequences of rational numbers

```agda
module elementary-number-theory.sums-of-finite-sequences-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.function-types
open import foundation.identity-types

open import lists.finite-sequences

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence of rational numbers" Agda=sum-fin-sequence-ℝ}}
extends [addition](elementary-number-theory.addition-rational-numbers.md) on the
[rational numbers](elementary-number-theory.rational-numbers.md) to any
[finite sequence](lists.finite-sequences.md) of rational numbers.

## Definition

```agda
sum-fin-sequence-ℚ : (n : ℕ) → fin-sequence ℚ n → ℚ
sum-fin-sequence-ℚ = sum-fin-sequence-type-Commutative-Ring commutative-ring-ℚ
```

## Properties

### The sum of a constant sequence is multiplication by a natural number

```agda
abstract
  sum-constant-fin-sequence-ℚ :
    (n : ℕ) (q : ℚ) →
    sum-fin-sequence-ℚ n (λ _ → q) ＝ rational-ℕ n *ℚ q
  sum-constant-fin-sequence-ℚ n q =
    sum-constant-fin-sequence-type-Commutative-Ring commutative-ring-ℚ n q ∙
    inv (left-mul-rational-nat-ℚ n q)
```

### If `aₙ ≤ bₙ` for each `n`, `Σ aₙ ≤ Σ bₙ`

```agda
abstract
  preserves-leq-sum-fin-sequence-ℚ :
    (n : ℕ) (a b : fin-sequence ℚ n) → ((k : Fin n) → leq-ℚ (a k) (b k)) →
    leq-ℚ (sum-fin-sequence-ℚ n a) (sum-fin-sequence-ℚ n b)
  preserves-leq-sum-fin-sequence-ℚ 0 _ _ _ = refl-leq-ℚ zero-ℚ
  preserves-leq-sum-fin-sequence-ℚ (succ-ℕ n) a b H =
    preserves-leq-add-ℚ
      ( preserves-leq-sum-fin-sequence-ℚ
        ( n)
        ( a ∘ inl-Fin n)
        ( b ∘ inl-Fin n)
        ( H ∘ inl-Fin n))
      ( H (neg-one-Fin n))
```

### Multiplication is distributive over sums on finite sequences

```agda
abstract
  left-distributive-mul-sum-fin-sequence-ℚ :
    (n : ℕ) (q : ℚ) (a : fin-sequence ℚ n) →
    q *ℚ sum-fin-sequence-ℚ n a ＝ sum-fin-sequence-ℚ n (mul-ℚ q ∘ a)
  left-distributive-mul-sum-fin-sequence-ℚ =
    left-distributive-mul-sum-fin-sequence-type-Commutative-Ring
      ( commutative-ring-ℚ)
```

### Splitting sums of `n + m` elements into a sum of `n` elements and a sum of `m` elements

```agda
split-sum-fin-sequence-ℚ :
  (n m : ℕ) (f : fin-sequence ℚ (n +ℕ m)) →
  sum-fin-sequence-ℚ (n +ℕ m) f ＝
  sum-fin-sequence-ℚ n (f ∘ inl-coproduct-Fin n m) +ℚ
  sum-fin-sequence-ℚ m (f ∘ inr-coproduct-Fin n m)
split-sum-fin-sequence-ℚ =
  split-sum-fin-sequence-type-Commutative-Ring commutative-ring-ℚ
```

### The sum of a single element is the single element

```agda
compute-sum-one-element-ℚ :
  (a : fin-sequence ℚ 1) → sum-fin-sequence-ℚ 1 a ＝ a (zero-Fin 0)
compute-sum-one-element-ℚ =
  compute-sum-one-element-Commutative-Ring commutative-ring-ℚ
```
