# Powers of nonnegative rational numbers

```agda
module elementary-number-theory.powers-nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequalities-positive-and-negative-rational-numbers
open import elementary-number-theory.inequality-nonnegative-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-monoid-of-nonnegative-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-nonnegative-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types

open import group-theory.powers-of-elements-commutative-monoids
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="a nonnegative rational number to a natural number power" Agda=power-ℚ⁰⁺}}
on the [nonnegative](elementary-number-theory.nonnegative-rational-numbers.md)
[rational numbers](elementary-number-theory.rational-numbers.md) is the
operation `n x ↦ xⁿ`, which is defined by
[iteratively](foundation.iterating-functions.md) multiplying `x` with itself `n`
times. This file covers the case where `n` is a
[natural number](elementary-number-theory.natural-numbers.md).

## Definition

```agda
power-ℚ⁰⁺ : ℕ → ℚ⁰⁺ → ℚ⁰⁺
power-ℚ⁰⁺ = power-Commutative-Monoid commutative-monoid-mul-ℚ⁰⁺
```

## Properties

### `1ⁿ = 1`

```agda
power-one-ℚ⁰⁺ : (n : ℕ) → power-ℚ⁰⁺ n one-ℚ⁰⁺ ＝ one-ℚ⁰⁺
power-one-ℚ⁰⁺ = power-unit-Commutative-Monoid commutative-monoid-mul-ℚ⁰⁺
```

### `qⁿ⁺¹ = qⁿq`

```agda
power-succ-ℚ⁰⁺ :
  (n : ℕ) (q : ℚ⁰⁺) → power-ℚ⁰⁺ (succ-ℕ n) q ＝ power-ℚ⁰⁺ n q *ℚ⁰⁺ q
power-succ-ℚ⁰⁺ = power-succ-Commutative-Monoid commutative-monoid-mul-ℚ⁰⁺
```

### `qⁿ = qqⁿ`

```agda
power-succ-ℚ⁰⁺' :
  (n : ℕ) (q : ℚ⁰⁺) → power-ℚ⁰⁺ (succ-ℕ n) q ＝ q *ℚ⁰⁺ power-ℚ⁰⁺ n q
power-succ-ℚ⁰⁺' = power-succ-Commutative-Monoid' commutative-monoid-mul-ℚ⁰⁺
```

### `qᵐ⁺ⁿ = qᵐqⁿ`

```agda
abstract
  distributive-power-add-ℚ⁰⁺ :
    (m n : ℕ) (q : ℚ⁰⁺) →
    power-ℚ⁰⁺ (m +ℕ n) q ＝ power-ℚ⁰⁺ m q *ℚ⁰⁺ power-ℚ⁰⁺ n q
  distributive-power-add-ℚ⁰⁺ m n _ =
    distributive-power-add-Commutative-Monoid commutative-monoid-mul-ℚ⁰⁺ m n
```

### `(pq)ⁿ=pⁿqⁿ`

```agda
abstract
  left-distributive-power-mul-ℚ⁰⁺ :
    (n : ℕ) (p q : ℚ⁰⁺) →
    power-ℚ⁰⁺ n (p *ℚ⁰⁺ q) ＝ power-ℚ⁰⁺ n p *ℚ⁰⁺ power-ℚ⁰⁺ n q
  left-distributive-power-mul-ℚ⁰⁺ n p q =
    distributive-power-mul-Commutative-Monoid commutative-monoid-mul-ℚ⁰⁺ n
```

### `pᵐⁿ = (pᵐ)ⁿ`

```agda
power-mul-ℚ⁰⁺ :
  (m n : ℕ) (q : ℚ⁰⁺) → power-ℚ⁰⁺ (m *ℕ n) q ＝ power-ℚ⁰⁺ n (power-ℚ⁰⁺ m q)
power-mul-ℚ⁰⁺ m n q =
  power-mul-Commutative-Monoid commutative-monoid-mul-ℚ⁰⁺ m n
```

### If `p` and `q` are nonnegative rational numbers with `p < q` and `n` is nonzero, then `pⁿ < qⁿ`

```agda
abstract
  preserves-le-power-ℚ⁰⁺ :
    (n : ℕ) → (p q : ℚ⁰⁺) → le-ℚ⁰⁺ p q → (is-nonzero-ℕ n) →
    le-ℚ⁰⁺ (power-ℚ⁰⁺ n p) (power-ℚ⁰⁺ n q)
  preserves-le-power-ℚ⁰⁺ 0 p q p<q H = ex-falso (H refl)
  preserves-le-power-ℚ⁰⁺ 1 p q p<q _ = p<q
  preserves-le-power-ℚ⁰⁺ (succ-ℕ n@(succ-ℕ _)) p q p<q _ =
    concatenate-leq-le-ℚ⁰⁺
      ( power-ℚ⁰⁺ (succ-ℕ n) p)
      ( power-ℚ⁰⁺ n p *ℚ⁰⁺ q)
      ( power-ℚ⁰⁺ (succ-ℕ n) q)
      ( preserves-leq-left-mul-ℚ⁰⁺ (power-ℚ⁰⁺ n p) _ _ (leq-le-ℚ p<q))
      ( preserves-le-right-mul-ℚ⁺
        ( rational-ℚ⁰⁺ q , is-positive-le-ℚ⁰⁺ p p<q)
        ( rational-ℚ⁰⁺ (power-ℚ⁰⁺ n p))
        ( rational-ℚ⁰⁺ (power-ℚ⁰⁺ n q))
        ( preserves-le-power-ℚ⁰⁺ n p q p<q (is-nonzero-succ-ℕ _)))
```

### If `p` and `q` are nonnegative rational numbers with `p ≤ q`, then `pⁿ ≤ qⁿ`

```agda
abstract
  preserves-leq-power-ℚ⁰⁺ :
    (n : ℕ) (p q : ℚ⁰⁺) → leq-ℚ⁰⁺ p q → leq-ℚ⁰⁺ (power-ℚ⁰⁺ n p) (power-ℚ⁰⁺ n q)
  preserves-leq-power-ℚ⁰⁺ 0 _ _ _ = refl-leq-ℚ one-ℚ
  preserves-leq-power-ℚ⁰⁺ 1 p q p≤q = p≤q
  preserves-leq-power-ℚ⁰⁺ (succ-ℕ n@(succ-ℕ _)) p q p≤q =
    transitive-leq-ℚ⁰⁺
      ( power-ℚ⁰⁺ (succ-ℕ n) p)
      ( power-ℚ⁰⁺ n p *ℚ⁰⁺ q)
      ( power-ℚ⁰⁺ (succ-ℕ n) q)
      ( preserves-leq-right-mul-ℚ⁰⁺ q _ _ (preserves-leq-power-ℚ⁰⁺ n p q p≤q))
      ( preserves-leq-left-mul-ℚ⁰⁺ (power-ℚ⁰⁺ n p) _ _ p≤q)
```
