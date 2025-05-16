# The binomial theorem for the integers

```agda
module elementary-number-theory.binomial-theorem-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.binomial-theorem-commutative-rings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.powers-integers
open import elementary-number-theory.ring-of-integers

open import foundation.homotopies
open import foundation.identity-types

open import lists.finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The binomial theorem for the integers asserts that for any two integers `x` and
`y` and any natural number `n`, we have

```text
  (x + y)ⁿ = ∑_{0 ≤ i < n+1} (n choose i) xⁱ yⁿ⁻ⁱ.
```

The binomial theorem is the [44th](literature.100-theorems.md#44) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Definitions

### Binomial sums

```agda
binomial-sum-ℤ : (n : ℕ) (f : fin-sequence ℤ (succ-ℕ n)) → ℤ
binomial-sum-ℤ =
  binomial-sum-fin-sequence-type-Commutative-Ring ℤ-Commutative-Ring
```

## Properties

### Binomial sums of one and two elements

```agda
binomial-sum-one-element-ℤ :
  (f : fin-sequence ℤ 1) → binomial-sum-ℤ 0 f ＝ head-fin-sequence 0 f
binomial-sum-one-element-ℤ =
  binomial-sum-one-element-Commutative-Ring ℤ-Commutative-Ring

binomial-sum-two-elements-ℤ :
  (f : fin-sequence ℤ 2) →
  binomial-sum-ℤ 1 f ＝ (f (zero-Fin 1)) +ℤ (f (one-Fin 1))
binomial-sum-two-elements-ℤ =
  binomial-sum-two-elements-Commutative-Ring ℤ-Commutative-Ring
```

### Binomial sums are homotopy invariant

```agda
htpy-binomial-sum-ℤ :
  (n : ℕ) {f g : fin-sequence ℤ (succ-ℕ n)} →
  (f ~ g) → binomial-sum-ℤ n f ＝ binomial-sum-ℤ n g
htpy-binomial-sum-ℤ =
  htpy-binomial-sum-fin-sequence-type-Commutative-Ring ℤ-Commutative-Ring
```

### Multiplication distributes over sums

```agda
left-distributive-mul-binomial-sum-ℤ :
  (n : ℕ) (x : ℤ) (f : fin-sequence ℤ (succ-ℕ n)) →
  x *ℤ (binomial-sum-ℤ n f) ＝ binomial-sum-ℤ n (λ i → x *ℤ (f i))
left-distributive-mul-binomial-sum-ℤ =
  left-distributive-mul-binomial-sum-fin-sequence-type-Commutative-Ring
    ℤ-Commutative-Ring

right-distributive-mul-binomial-sum-ℤ :
  (n : ℕ) (f : fin-sequence ℤ (succ-ℕ n)) (x : ℤ) →
  (binomial-sum-ℤ n f) *ℤ x ＝ binomial-sum-ℤ n (λ i → (f i) *ℤ x)
right-distributive-mul-binomial-sum-ℤ =
  right-distributive-mul-binomial-sum-fin-sequence-type-Commutative-Ring
    ℤ-Commutative-Ring
```

## Theorem

### Binomial theorem for the integers

```agda
binomial-theorem-ℤ :
  (n : ℕ) (x y : ℤ) →
  power-ℤ n (x +ℤ y) ＝
  binomial-sum-ℤ n
    ( λ i →
        ( power-ℤ (nat-Fin (succ-ℕ n) i) x) *ℤ
        ( power-ℤ (dist-ℕ (nat-Fin (succ-ℕ n) i) n) y))
binomial-theorem-ℤ = binomial-theorem-Commutative-Ring ℤ-Commutative-Ring
```

## References

{{#bibliography}}
