# The binomial theorem for the integers

```agda
module elementary-number-theory.binomial-theorem-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.binomial-theorem-commutative-rings
open import commutative-algebra.commutative-semirings
open import commutative-algebra.powers-of-elements-commutative-semirings
open import commutative-algebra.sums-commutative-semirings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.commutative-ring-of-integers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.powers-integers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The binomial theorem for the integers asserts that for any two integers `x` and `y` and any natural number `n`, we have

```md
  (x + y)ⁿ = ∑_{0 ≤ i < n+1} (n choose i) xⁱ yⁿ⁻ⁱ.
```

## Definitions

### Binomial sums

```agda
binomial-sum-ℤ : (n : ℕ) (f : functional-vec ℤ (succ-ℕ n)) → ℤ
binomial-sum-ℤ = binomial-sum-Commutative-Ring ℤ-Commutative-Ring
```

## Properties

### Binomial sums of one and two elements

```agda
binomial-sum-one-element-ℤ :
  (f : functional-vec ℤ 1) → binomial-sum-ℤ 0 f ＝ head-functional-vec 0 f
binomial-sum-one-element-ℤ =
  binomial-sum-one-element-Commutative-Ring ℤ-Commutative-Ring

binomial-sum-two-elements-ℤ :
  (f : functional-vec ℤ 2) →
  binomial-sum-ℤ 1 f ＝ add-ℤ (f (zero-Fin 1)) (f (one-Fin 1))
binomial-sum-two-elements-ℤ =
  binomial-sum-two-elements-Commutative-Ring ℤ-Commutative-Ring
```

### Binomial sums are homotopy invariant

```agda
htpy-binomial-sum-ℤ :
  (n : ℕ) {f g : functional-vec ℤ (succ-ℕ n)} →
  (f ~ g) → binomial-sum-ℤ n f ＝ binomial-sum-ℤ n g
htpy-binomial-sum-ℤ =
  htpy-binomial-sum-Commutative-Ring ℤ-Commutative-Ring
```

### Multiplication distributes over sums

```agda
left-distributive-mul-binomial-sum-ℤ :
  (n : ℕ) (x : ℤ) (f : functional-vec ℤ (succ-ℕ n)) →
  mul-ℤ x (binomial-sum-ℤ n f) ＝ binomial-sum-ℤ n (λ i → mul-ℤ x (f i))
left-distributive-mul-binomial-sum-ℤ =
  left-distributive-mul-binomial-sum-Commutative-Ring ℤ-Commutative-Ring

right-distributive-mul-binomial-sum-ℤ :
  (n : ℕ) (f : functional-vec ℤ (succ-ℕ n)) (x : ℤ) →
  mul-ℤ (binomial-sum-ℤ n f) x ＝ binomial-sum-ℤ n (λ i → mul-ℤ (f i) x)
right-distributive-mul-binomial-sum-ℤ =
  right-distributive-mul-binomial-sum-Commutative-Ring
    ℤ-Commutative-Ring
```

## Theorem

### Binomial theorem for the integers

```agda
binomial-theorem-ℤ :
  (n : ℕ) (x y : ℤ) →
  power-ℤ n (add-ℤ x y) ＝
  binomial-sum-ℤ n
    ( λ i →
      mul-ℤ
      ( power-ℤ (nat-Fin (succ-ℕ n) i) x)
      ( power-ℤ (dist-ℕ n (nat-Fin (succ-ℕ n) i)) y))
binomial-theorem-ℤ = binomial-theorem-Commutative-Ring ℤ-Commutative-Ring
```
