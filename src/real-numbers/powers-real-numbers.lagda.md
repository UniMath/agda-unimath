# Powers of real numbers

```agda
module real-numbers.powers-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.powers-of-elements-large-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.powers-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.large-ring-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising a real number to a natural number power" Agda=power-ℝ}}
on the [real numbers](real-numbers.dedekind-real-numbers.md) `n x ↦ xⁿ`, is
defined by [iteratively](foundation.iterating-functions.md)
[multiplying](real-numbers.multiplication-real-numbers.md) `x` with itself `n`
times.

## Definition

```agda
power-ℝ : {l : Level} → ℕ → ℝ l → ℝ l
power-ℝ = power-Large-Commutative-Ring large-commutative-ring-ℝ
```

## Properties

### The canonical embedding of rational numbers preserves powers

```agda
abstract
  power-real-ℚ : (n : ℕ) (q : ℚ) → power-ℝ n (real-ℚ q) ＝ real-ℚ (power-ℚ n q)
  power-real-ℚ n q =
    inv
      ( preserves-powers-hom-Commutative-Ring
        ( commutative-ring-ℚ)
        ( commutative-ring-ℝ lzero)
        ( hom-ring-real-ℚ)
        ( n)
        ( q))
```

### `1ⁿ ＝ 1`

```agda
abstract
  power-one-ℝ : (n : ℕ) → power-ℝ n one-ℝ ＝ one-ℝ
  power-one-ℝ = power-one-Large-Commutative-Ring large-commutative-ring-ℝ
```

### `xⁿ⁺¹ = xⁿx`

```agda
abstract
  power-succ-ℝ :
    {l : Level} (n : ℕ) (x : ℝ l) → power-ℝ (succ-ℕ n) x ＝ power-ℝ n x *ℝ x
  power-succ-ℝ = power-succ-Large-Commutative-Ring large-commutative-ring-ℝ
```

### `xⁿ⁺¹ = xxⁿ`

```agda
abstract
  power-succ-ℝ' :
    {l : Level} (n : ℕ) (x : ℝ l) → power-ℝ (succ-ℕ n) x ＝ x *ℝ power-ℝ n x
  power-succ-ℝ' = power-succ-Large-Commutative-Ring' large-commutative-ring-ℝ
```

### Powers by sums of natural numbers are products of powers

```agda
abstract
  distributive-power-add-ℝ :
    {l : Level} (m n : ℕ) {x : ℝ l} →
    power-ℝ (m +ℕ n) x ＝ power-ℝ m x *ℝ power-ℝ n x
  distributive-power-add-ℝ =
    distributive-power-add-Large-Commutative-Ring large-commutative-ring-ℝ
```

### Powers by products of natural numbers are iterated powers

```agda
abstract
  power-mul-ℝ :
    {l : Level} (m n : ℕ) {x : ℝ l} →
    power-ℝ (m *ℕ n) x ＝ power-ℝ n (power-ℝ m x)
  power-mul-ℝ =
    power-mul-Large-Commutative-Ring large-commutative-ring-ℝ
```

### `(xy)ⁿ = xⁿyⁿ`

```agda
abstract
  distributive-power-mul-ℝ :
    {l1 l2 : Level} (n : ℕ) {x : ℝ l1} {y : ℝ l2} →
    power-ℝ n (x *ℝ y) ＝ power-ℝ n x *ℝ power-ℝ n y
  distributive-power-mul-ℝ =
    distributive-power-mul-Large-Commutative-Ring large-commutative-ring-ℝ
```
