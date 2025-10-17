# Powers of rational numbers

```agda
module elementary-number-theory.powers-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-nonnegative-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-positive-and-negative-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.squares-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications

open import group-theory.powers-of-elements-commutative-monoids
open import group-theory.powers-of-elements-monoids
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising a rational number to a natural number power" Agda=power-ℚ}}
on the [rational numbers](elementary-number-theory.rational-numbers.md)
`n x ↦ xⁿ`, is defined by [iteratively](foundation.iterating-functions.md)
multiplying `x` with itself `n` times.

## Definition

```agda
power-ℚ : ℕ → ℚ → ℚ
power-ℚ = power-Monoid monoid-mul-ℚ
```

## Properties

### `1ⁿ = 1`

```agda
abstract
  power-one-ℚ : (n : ℕ) → power-ℚ n one-ℚ ＝ one-ℚ
  power-one-ℚ = power-unit-Monoid monoid-mul-ℚ
```

### `qⁿ¹ = qⁿq`

```agda
abstract
  power-succ-ℚ : (n : ℕ) (q : ℚ) → power-ℚ (succ-ℕ n) q ＝ power-ℚ n q *ℚ q
  power-succ-ℚ = power-succ-Monoid monoid-mul-ℚ
```

### `qⁿ = qqⁿ`

```agda
abstract
  power-succ-ℚ' : (n : ℕ) (q : ℚ) → power-ℚ (succ-ℕ n) q ＝ q *ℚ power-ℚ n q
  power-succ-ℚ' = power-succ-Monoid' monoid-mul-ℚ
```

### `qᵐⁿ = qᵐqⁿ`

```agda
abstract
  distributive-power-add-ℚ :
    (m n : ℕ) (q : ℚ) → power-ℚ (m +ℕ n) q ＝ power-ℚ m q *ℚ power-ℚ n q
  distributive-power-add-ℚ m n _ =
    distributive-power-add-Monoid monoid-mul-ℚ m n
```

### `(pq)ⁿ=pⁿqⁿ`

```agda
abstract
  left-distributive-power-mul-ℚ :
    (n : ℕ) (p q : ℚ) → power-ℚ n (p *ℚ q) ＝ power-ℚ n p *ℚ power-ℚ n q
  left-distributive-power-mul-ℚ n p q =
    distributive-power-mul-Commutative-Monoid commutative-monoid-mul-ℚ n
```

### `pᵐⁿ = (pᵐ)ⁿ`

```agda
abstract
  power-mul-ℚ :
    (m n : ℕ) (q : ℚ) → power-ℚ (m *ℕ n) q ＝ power-ℚ n (power-ℚ m q)
  power-mul-ℚ m n q = power-mul-Monoid monoid-mul-ℚ m n
```

### Even powers of rational numbers are nonnegative

```agda
abstract
  is-nonnegative-even-power-ℚ :
    (n : ℕ) (q : ℚ) → is-even-ℕ n → is-nonnegative-ℚ (power-ℚ n q)
  is-nonnegative-even-power-ℚ _ q (k , refl) =
    inv-tr
      ( is-nonnegative-ℚ)
      ( power-mul-ℚ k 2 q)
      ( is-nonnegative-square-ℚ (power-ℚ k q))

nonnegative-even-power-ℚ :
  (n : ℕ) (q : ℚ) → is-even-ℕ n → ℚ⁰⁺
nonnegative-even-power-ℚ n q even-n =
  ( power-ℚ n q , is-nonnegative-even-power-ℚ n q even-n)
```

### Powers of positive rational numbers are positive

```agda
abstract
  is-positive-power-ℚ⁺ :
    (n : ℕ) (q : ℚ⁺) → is-positive-ℚ (power-ℚ n (rational-ℚ⁺ q))
  is-positive-power-ℚ⁺ 0 q = is-positive-rational-ℚ⁺ one-ℚ⁺
  is-positive-power-ℚ⁺ (succ-ℕ n) q⁺@(q , is-pos-q) =
    inv-tr
      ( is-positive-ℚ)
      ( power-succ-ℚ n q)
      ( is-positive-mul-ℚ (is-positive-power-ℚ⁺ n q⁺) is-pos-q)
```

### Even powers of negative rational numbers are positive

```agda
abstract
  is-positive-even-power-ℚ⁻ :
    (n : ℕ) (q : ℚ⁻) → is-even-ℕ n → is-positive-ℚ (power-ℚ n (rational-ℚ⁻ q))
  is-positive-even-power-ℚ⁻ _ q⁻@(q , is-neg-q) (k , refl) =
    inv-tr
      ( is-positive-ℚ)
      ( equational-reasoning
        power-ℚ (k *ℕ 2) q
        ＝ power-ℚ (2 *ℕ k) q
          by ap (λ m → power-ℚ m q) (commutative-mul-ℕ k 2)
        ＝ power-ℚ k (square-ℚ q)
          by power-mul-ℚ 2 k q)
      ( is-positive-power-ℚ⁺ k (square-ℚ⁻ q⁻))
```

### Odd powers of negative rational numbers are negative

```agda
abstract
  is-negative-odd-power-ℚ⁻ :
    (n : ℕ) (q : ℚ⁻) → is-odd-ℕ n → is-negative-ℚ (power-ℚ n (rational-ℚ⁻ q))
  is-negative-odd-power-ℚ⁻ n q⁻@(q , is-neg-q) odd-n =
    let
      (k , k2+1=n) = has-odd-expansion-is-odd n odd-n
    in
      tr
        ( is-negative-ℚ)
        ( equational-reasoning
          power-ℚ (k *ℕ 2) q *ℚ q
          ＝ power-ℚ (succ-ℕ (k *ℕ 2)) q
            by inv (power-succ-ℚ (k *ℕ 2) q)
          ＝ power-ℚ n q
            by ap (λ m → power-ℚ m q) k2+1=n)
        ( is-negative-mul-positive-negative-ℚ
          ( is-positive-even-power-ℚ⁻ (k *ℕ 2) q⁻ (k , refl))
          ( is-neg-q))
```

### If `|p| ≤ |q|`, `|pⁿ| ≤ |qⁿ|`

```agda
abstract
  preserves-leq-abs-power-ℚ :
    (n : ℕ) (p q : ℚ) → leq-ℚ⁰⁺ (abs-ℚ p) (abs-ℚ q) →
    leq-ℚ⁰⁺ (abs-ℚ (power-ℚ n p)) (abs-ℚ (power-ℚ n q))
  preserves-leq-abs-power-ℚ 0 p q _ = refl-leq-ℚ _
  preserves-leq-abs-power-ℚ (succ-ℕ n) p q |p|≤|q| =
    binary-tr
      ( leq-ℚ)
      ( equational-reasoning
        rational-abs-ℚ (power-ℚ n p) *ℚ rational-abs-ℚ p
        ＝ rational-abs-ℚ (power-ℚ n p *ℚ p)
          by inv (rational-abs-mul-ℚ (power-ℚ n p) p)
        ＝ rational-abs-ℚ (power-ℚ (succ-ℕ n) p)
          by ap rational-abs-ℚ (inv (power-succ-ℚ n p)))
      ( equational-reasoning
        rational-abs-ℚ (power-ℚ n q) *ℚ rational-abs-ℚ q
        ＝ rational-abs-ℚ (power-ℚ n q *ℚ q)
          by inv (rational-abs-mul-ℚ (power-ℚ n q) q)
        ＝ rational-abs-ℚ (power-ℚ (succ-ℕ n) q)
          by ap rational-abs-ℚ (inv (power-succ-ℚ n q)))
      ( preserves-leq-mul-ℚ⁰⁺
        ( abs-ℚ (power-ℚ n p))
        ( abs-ℚ (power-ℚ n q))
        ( abs-ℚ p)
        ( abs-ℚ q)
        ( preserves-leq-abs-power-ℚ n p q |p|≤|q|)
        ( |p|≤|q|))
```

## See also

- [Powers of elements of a monoid](group-theory.powers-of-elements-monoids.md)
- [Powers of elements of a commutative monoid](group-theory.powers-of-elements-commutative-monoids.md)
