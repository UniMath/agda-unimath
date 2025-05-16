# The binomial theorem for the natural numbers

```agda
module elementary-number-theory.binomial-theorem-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.binomial-theorem-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.commutative-semiring-of-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.homotopies
open import foundation.identity-types

open import lists.finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The binomial theorem for natural numbers asserts that for any two natural
numbers `x` and `y` and any natural number `n`, we have

```text
  (x + y)ⁿ = ∑_{0 ≤ i < n+1} (n choose i) xⁱ yⁿ⁻ⁱ.
```

The binomial theorem is the [44th](literature.100-theorems.md#44) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Definitions

### Binomial sums

```agda
binomial-sum-ℕ : (n : ℕ) (f : fin-sequence ℕ (succ-ℕ n)) → ℕ
binomial-sum-ℕ =
  binomial-sum-fin-sequence-type-Commutative-Semiring ℕ-Commutative-Semiring
```

## Properties

### Binomial sums of one and two elements

```agda
binomial-sum-one-element-ℕ :
  (f : fin-sequence ℕ 1) → binomial-sum-ℕ 0 f ＝ head-fin-sequence 0 f
binomial-sum-one-element-ℕ =
  binomial-sum-one-element-Commutative-Semiring ℕ-Commutative-Semiring

binomial-sum-two-elements-ℕ :
  (f : fin-sequence ℕ 2) →
  binomial-sum-ℕ 1 f ＝ (f (zero-Fin 1)) +ℕ (f (one-Fin 1))
binomial-sum-two-elements-ℕ =
  binomial-sum-two-elements-Commutative-Semiring ℕ-Commutative-Semiring
```

### Binomial sums are homotopy invariant

```agda
htpy-binomial-sum-ℕ :
  (n : ℕ) {f g : fin-sequence ℕ (succ-ℕ n)} →
  (f ~ g) → binomial-sum-ℕ n f ＝ binomial-sum-ℕ n g
htpy-binomial-sum-ℕ =
  htpy-binomial-sum-fin-sequence-type-Commutative-Semiring
    ℕ-Commutative-Semiring
```

### Multiplication distributes over sums

```agda
left-distributive-mul-binomial-sum-ℕ :
  (n : ℕ) (x : ℕ) (f : fin-sequence ℕ (succ-ℕ n)) →
  x *ℕ (binomial-sum-ℕ n f) ＝ binomial-sum-ℕ n (λ i → x *ℕ (f i))
left-distributive-mul-binomial-sum-ℕ =
  left-distributive-mul-binomial-sum-fin-sequence-type-Commutative-Semiring
    ℕ-Commutative-Semiring

right-distributive-mul-binomial-sum-ℕ :
  (n : ℕ) (f : fin-sequence ℕ (succ-ℕ n)) (x : ℕ) →
  (binomial-sum-ℕ n f) *ℕ x ＝ binomial-sum-ℕ n (λ i → (f i) *ℕ x)
right-distributive-mul-binomial-sum-ℕ =
  right-distributive-mul-binomial-sum-fin-sequence-type-Commutative-Semiring
    ℕ-Commutative-Semiring
```

## Theorem

### Binomial theorem for the natural numbers

```agda
binomial-theorem-ℕ :
  (n : ℕ) (x y : ℕ) →
  power-ℕ n (x +ℕ y) ＝
  binomial-sum-ℕ n
    ( λ i →
      ( power-ℕ (nat-Fin (succ-ℕ n) i) x) *ℕ
      ( power-ℕ (dist-ℕ (nat-Fin (succ-ℕ n) i) n) y))
binomial-theorem-ℕ =
  binomial-theorem-Commutative-Semiring ℕ-Commutative-Semiring
```

## References

{{#bibliography}}
