# Powers of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.powers-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequalities-positive-and-negative-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-nonnegative-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-positive-and-negative-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.powers-nonnegative-rational-numbers
open import elementary-number-theory.powers-positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.squares-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.transport-along-identifications

open import group-theory.powers-of-elements-commutative-monoids
open import group-theory.powers-of-elements-monoids

open import logic.functoriality-existential-quantification

open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.rational-sequences-approximating-zero

open import order-theory.cofinal-maps-posets
open import order-theory.coinitial-maps-posets
open import order-theory.posets
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

### The power operation on rational numbers agrees with the power operation on positive rational numbers

```agda
abstract
  power-rational-ℚ⁺ :
    (n : ℕ) (q : ℚ⁺) → power-ℚ n (rational-ℚ⁺ q) ＝ rational-ℚ⁺ (power-ℚ⁺ n q)
  power-rational-ℚ⁺ 0 _ = refl
  power-rational-ℚ⁺ 1 _ = refl
  power-rational-ℚ⁺ (succ-ℕ n@(succ-ℕ _)) q =
    ap-mul-ℚ (power-rational-ℚ⁺ n q) refl
```

### The power operation on rational numbers agrees with the power operation on nonnegative rational numbers

```agda
abstract
  power-rational-ℚ⁰⁺ :
    (n : ℕ) (q : ℚ⁰⁺) →
    power-ℚ n (rational-ℚ⁰⁺ q) ＝ rational-ℚ⁰⁺ (power-ℚ⁰⁺ n q)
  power-rational-ℚ⁰⁺ 0 _ = refl
  power-rational-ℚ⁰⁺ 1 _ = refl
  power-rational-ℚ⁰⁺ (succ-ℕ n@(succ-ℕ _)) q =
    ap-mul-ℚ (power-rational-ℚ⁰⁺ n q) refl
```

### `1ⁿ = 1`

```agda
abstract
  power-one-ℚ : (n : ℕ) → power-ℚ n one-ℚ ＝ one-ℚ
  power-one-ℚ = power-unit-Monoid monoid-mul-ℚ
```

### `qⁿ⁺¹ = qⁿq`

```agda
abstract
  power-succ-ℚ : (n : ℕ) (q : ℚ) → power-ℚ (succ-ℕ n) q ＝ power-ℚ n q *ℚ q
  power-succ-ℚ = power-succ-Monoid monoid-mul-ℚ
```

### `0ⁿ = 0` when `1 ≤ n`

```agda
abstract
  power-zero-ℚ : (n : ℕ) → leq-ℕ 1 n → power-ℚ n zero-ℚ ＝ zero-ℚ
  power-zero-ℚ (succ-ℕ n) _ = power-succ-ℚ n _ ∙ right-zero-law-mul-ℚ _
```

### `qⁿ⁺¹ = qqⁿ`

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

  power-mul-ℚ' :
    (m n : ℕ) (q : ℚ) → power-ℚ (m *ℕ n) q ＝ power-ℚ m (power-ℚ n q)
  power-mul-ℚ' m n q =
    ap (λ k → power-ℚ k q) (commutative-mul-ℕ m n) ∙ power-mul-ℚ n m q
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
  is-positive-power-ℚ⁺ n q =
    inv-tr
      ( is-positive-ℚ)
      ( power-rational-ℚ⁺ n q)
      ( is-positive-rational-ℚ⁺ (power-ℚ⁺ n q))
```

### Even powers of negative rational numbers are positive

```agda
abstract
  is-positive-even-power-ℚ⁻ :
    (n : ℕ) (q : ℚ⁻) → is-even-ℕ n → is-positive-ℚ (power-ℚ n (rational-ℚ⁻ q))
  is-positive-even-power-ℚ⁻ _ q⁻@(q , is-neg-q) (k , refl) =
    inv-tr
      ( is-positive-ℚ)
      ( power-mul-ℚ' k 2 q)
      ( is-positive-power-ℚ⁺ k (square-ℚ⁻ q⁻))
```

### Odd powers of negative rational numbers are negative

```agda
abstract
  is-negative-power-is-odd-exponent-ℚ⁻ :
    (n : ℕ) (q : ℚ⁻) → is-odd-ℕ n → is-negative-ℚ (power-ℚ n (rational-ℚ⁻ q))
  is-negative-power-is-odd-exponent-ℚ⁻ n q⁻@(q , is-neg-q) odd-n =
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

### For even `n`, `(-q)ⁿ = qⁿ`

```agda
abstract
  power-neg-is-even-exponent-ℚ :
    (n : ℕ) (q : ℚ) → is-even-ℕ n → power-ℚ n (neg-ℚ q) ＝ power-ℚ n q
  power-neg-is-even-exponent-ℚ _ q (k , refl) =
    equational-reasoning
      power-ℚ (k *ℕ 2) (neg-ℚ q)
      ＝ power-ℚ k (square-ℚ (neg-ℚ q))
        by power-mul-ℚ' k 2 (neg-ℚ q)
      ＝ power-ℚ k (square-ℚ q)
        by ap (power-ℚ k) (square-neg-ℚ q)
      ＝ power-ℚ (k *ℕ 2) q
        by inv (power-mul-ℚ' k 2 q)
```

### For odd `n`, `(-q)ⁿ = -(qⁿ)`

```agda
abstract
  power-neg-is-odd-exponent-ℚ :
    (n : ℕ) (q : ℚ) → is-odd-ℕ n → power-ℚ n (neg-ℚ q) ＝ neg-ℚ (power-ℚ n q)
  power-neg-is-odd-exponent-ℚ n q odd-n =
    let (k , k2+1=n) = has-odd-expansion-is-odd n odd-n
    in
      equational-reasoning
        power-ℚ n (neg-ℚ q)
        ＝ power-ℚ (succ-ℕ (k *ℕ 2)) (neg-ℚ q)
          by ap (λ m → power-ℚ m (neg-ℚ q)) (inv k2+1=n)
        ＝ power-ℚ (k *ℕ 2) (neg-ℚ q) *ℚ neg-ℚ q
          by power-succ-ℚ (k *ℕ 2) (neg-ℚ q)
        ＝ power-ℚ (k *ℕ 2) q *ℚ neg-ℚ q
          by ap-mul-ℚ (power-neg-is-even-exponent-ℚ _ q (k , refl)) refl
        ＝ neg-ℚ (power-ℚ (k *ℕ 2) q *ℚ q)
          by right-negative-law-mul-ℚ _ _
        ＝ neg-ℚ (power-ℚ (succ-ℕ (k *ℕ 2)) q)
          by ap neg-ℚ (inv (power-succ-ℚ (k *ℕ 2) q))
        ＝ neg-ℚ (power-ℚ n q)
          by ap (λ m → neg-ℚ (power-ℚ m q)) k2+1=n

  neg-power-neg-is-odd-exponent-ℚ :
    (n : ℕ) (q : ℚ) → is-odd-ℕ n → neg-ℚ (power-ℚ n (neg-ℚ q)) ＝ power-ℚ n q
  neg-power-neg-is-odd-exponent-ℚ n q odd-n =
    ap neg-ℚ (power-neg-is-odd-exponent-ℚ n q odd-n) ∙ neg-neg-ℚ _

  neg-power-neg-is-odd-exponent-ℚ⁻ :
    (n : ℕ) (q : ℚ⁻) → is-odd-ℕ n →
    neg-ℚ (rational-ℚ⁺ (power-ℚ⁺ n (neg-ℚ⁻ q))) ＝ power-ℚ n (rational-ℚ⁻ q)
  neg-power-neg-is-odd-exponent-ℚ⁻ n q⁻@(q , _) odd-n =
    ( ap neg-ℚ (inv (power-rational-ℚ⁺ n _))) ∙
    ( neg-power-neg-is-odd-exponent-ℚ n q odd-n)
```

### `|q|ⁿ=|qⁿ|`

```agda
abstract
  power-rational-abs-ℚ :
    (n : ℕ) (q : ℚ) →
    power-ℚ n (rational-abs-ℚ q) ＝ rational-abs-ℚ (power-ℚ n q)
  power-rational-abs-ℚ 0 q = inv (ap rational-ℚ⁰⁺ (abs-rational-ℚ⁰⁺ one-ℚ⁰⁺))
  power-rational-abs-ℚ 1 q = refl
  power-rational-abs-ℚ (succ-ℕ n@(succ-ℕ _)) q =
    equational-reasoning
      power-ℚ n (rational-abs-ℚ q) *ℚ rational-abs-ℚ q
      ＝ rational-abs-ℚ (power-ℚ n q) *ℚ rational-abs-ℚ q
        by ap-mul-ℚ (power-rational-abs-ℚ n q) refl
      ＝ rational-abs-ℚ (power-ℚ n q *ℚ q)
        by inv (rational-abs-mul-ℚ _ _)
```

### If `|p| ≤ |q|`, then `|pⁿ| ≤ |qⁿ|`

```agda
abstract
  preserves-leq-abs-power-ℚ :
    (n : ℕ) (p q : ℚ) → leq-ℚ⁰⁺ (abs-ℚ p) (abs-ℚ q) →
    leq-ℚ⁰⁺ (abs-ℚ (power-ℚ n p)) (abs-ℚ (power-ℚ n q))
  preserves-leq-abs-power-ℚ n p q |p|≤|q| =
    binary-tr
      ( leq-ℚ)
      ( inv (power-rational-ℚ⁰⁺ n (abs-ℚ p)) ∙ power-rational-abs-ℚ n p)
      ( inv (power-rational-ℚ⁰⁺ n (abs-ℚ q)) ∙ power-rational-abs-ℚ n q)
      ( preserves-leq-power-ℚ⁰⁺ n (abs-ℚ p) (abs-ℚ q) |p|≤|q|)
```

### Odd powers of rational numbers preserve inequality

```agda
abstract
  preserves-leq-power-is-odd-exponent-ℚ :
    (n : ℕ) (p q : ℚ) → is-odd-ℕ n → leq-ℚ p q →
    leq-ℚ (power-ℚ n p) (power-ℚ n q)
  preserves-leq-power-is-odd-exponent-ℚ n p q odd-n p≤q =
    rec-coproduct
      ( λ is-neg-p →
        rec-coproduct
          ( λ is-neg-q →
            let
              p⁻ = (p , is-neg-p)
              q⁻ = (q , is-neg-q)
            in
              binary-tr
                ( leq-ℚ)
                ( neg-power-neg-is-odd-exponent-ℚ⁻ n p⁻ odd-n)
                ( neg-power-neg-is-odd-exponent-ℚ⁻ n q⁻ odd-n)
                ( neg-leq-ℚ
                  ( preserves-leq-power-ℚ⁺
                    ( n)
                    ( neg-ℚ⁻ q⁻)
                    ( neg-ℚ⁻ p⁻)
                    ( neg-leq-ℚ p≤q))))
          ( λ is-nonneg-q →
            inv-tr
              ( leq-ℚ (power-ℚ n p))
              ( power-rational-ℚ⁰⁺ n (q , is-nonneg-q))
              ( leq-negative-nonnegative-ℚ
                ( power-ℚ n p ,
                  is-negative-power-is-odd-exponent-ℚ⁻ n (p , is-neg-p) odd-n)
                ( power-ℚ⁰⁺ n (q , is-nonneg-q))))
          ( decide-is-negative-is-nonnegative-ℚ q))
      ( λ is-nonneg-p →
        let
          p⁰⁺ = (p , is-nonneg-p)
          q⁰⁺ = (q , is-nonnegative-leq-ℚ⁰⁺ p⁰⁺ q p≤q)
        in
          binary-tr
            ( leq-ℚ)
            ( inv (power-rational-ℚ⁰⁺ n p⁰⁺))
            ( inv (power-rational-ℚ⁰⁺ n q⁰⁺))
            ( preserves-leq-power-ℚ⁰⁺ n p⁰⁺ q⁰⁺ p≤q))
      ( decide-is-negative-is-nonnegative-ℚ p)
```

### Odd powers of rational numbers preserve strict inequality

```agda
abstract
  preserves-le-power-is-odd-exponent-ℚ :
    (n : ℕ) (p q : ℚ) → is-odd-ℕ n → le-ℚ p q →
    le-ℚ (power-ℚ n p) (power-ℚ n q)
  preserves-le-power-is-odd-exponent-ℚ n p q odd-n p<q =
    rec-coproduct
      ( λ is-neg-p →
        rec-coproduct
          ( λ is-neg-q →
            let
              p⁻ = (p , is-neg-p)
              q⁻ = (q , is-neg-q)
            in
              binary-tr
                ( le-ℚ)
                ( neg-power-neg-is-odd-exponent-ℚ⁻ n p⁻ odd-n)
                ( neg-power-neg-is-odd-exponent-ℚ⁻ n q⁻ odd-n)
                ( neg-le-ℚ
                  ( preserves-le-power-ℚ⁺
                    ( n)
                    ( neg-ℚ⁻ q⁻)
                    ( neg-ℚ⁻ p⁻)
                    ( neg-le-ℚ p<q)
                    ( is-nonzero-is-odd-ℕ odd-n))))
          ( λ is-nonneg-q →
            inv-tr
              ( le-ℚ (power-ℚ n p))
              ( power-rational-ℚ⁰⁺ n (q , is-nonneg-q))
              ( le-negative-nonnegative-ℚ
                ( power-ℚ n p ,
                  is-negative-power-is-odd-exponent-ℚ⁻ n (p , is-neg-p) odd-n)
                ( power-ℚ⁰⁺ n (q , is-nonneg-q))))
          ( decide-is-negative-is-nonnegative-ℚ q))
      ( λ is-nonneg-p →
        let
          p⁰⁺ = (p , is-nonneg-p)
          q⁰⁺ = (q , is-nonnegative-le-ℚ⁰⁺ p⁰⁺ q p<q)
        in
          binary-tr
            ( le-ℚ)
            ( inv (power-rational-ℚ⁰⁺ n p⁰⁺))
            ( inv (power-rational-ℚ⁰⁺ n q⁰⁺))
            ( preserves-le-power-ℚ⁰⁺ n p⁰⁺ q⁰⁺ p<q (is-nonzero-is-odd-ℕ odd-n)))
      ( decide-is-negative-is-nonnegative-ℚ p)
```

### If `|ε| < 1`, `εⁿ` approaches 0

```agda
abstract
  is-zero-limit-power-le-one-abs-ℚ :
    (ε : ℚ) → le-ℚ (rational-abs-ℚ ε) one-ℚ →
    is-zero-limit-sequence-ℚ (λ n → power-ℚ n ε)
  is-zero-limit-power-le-one-abs-ℚ ε |ε|<1 =
    trichotomy-sign-ℚ ε
      ( λ is-neg-ε →
        let
          ε⁻ = (ε , is-neg-ε)
        in
          is-zero-limit-is-zero-limit-abs-sequence-ℚ
            ( _)
            ( inv-tr
              ( is-zero-limit-sequence-ℚ)
              ( eq-htpy
                ( λ n →
                  equational-reasoning
                    rational-abs-ℚ (power-ℚ n ε)
                    ＝ power-ℚ n (rational-abs-ℚ ε)
                      by inv (power-rational-abs-ℚ n ε)
                    ＝ power-ℚ n (neg-ℚ ε)
                      by
                        ap (power-ℚ n) (rational-abs-rational-ℚ⁻ ε⁻)
                    ＝ rational-ℚ⁺ (power-ℚ⁺ n (neg-ℚ⁻ ε⁻))
                      by power-rational-ℚ⁺ n (neg-ℚ⁻ ε⁻)))
            ( is-zero-limit-power-le-one-ℚ⁺
              ( neg-ℚ⁻ ε⁻)
              ( tr
                ( λ q → le-ℚ q one-ℚ)
                ( rational-abs-rational-ℚ⁻ ε⁻)
                ( |ε|<1)))))
      ( λ ε=0 →
        is-limit-bound-modulus-sequence-Metric-Space
          ( metric-space-ℚ)
          ( λ n → power-ℚ n ε)
          ( zero-ℚ)
          ( λ δ →
            ( 1 ,
              λ n 1≤n →
                inv-tr
                  ( λ z → neighborhood-ℚ δ z zero-ℚ)
                  ( ap (power-ℚ n) ε=0 ∙ power-zero-ℚ n 1≤n)
                  ( is-reflexive-neighborhood-ℚ δ zero-ℚ))))
      ( λ is-pos-ε →
        inv-tr
          ( is-zero-limit-sequence-ℚ)
          ( eq-htpy (λ n → power-rational-ℚ⁺ n (ε , is-pos-ε)))
          ( is-zero-limit-power-le-one-ℚ⁺
            ( ε , is-pos-ε)
            ( tr
              ( λ q → le-ℚ q one-ℚ)
              ( rational-abs-rational-ℚ⁺ (ε , is-pos-ε))
              ( |ε|<1))))
```

### If `1 ≤ q` and `n` is nonzero, then `q ≤ qⁿ`

```agda
abstract
  leq-power-nonzero-leq-one-ℚ :
    (n : ℕ) → is-nonzero-ℕ n → (q : ℚ) → leq-ℚ one-ℚ q → leq-ℚ q (power-ℚ n q)
  leq-power-nonzero-leq-one-ℚ 0 H q 1≤q = ex-falso (H refl)
  leq-power-nonzero-leq-one-ℚ 1 _ q 1≤q = refl-leq-ℚ q
  leq-power-nonzero-leq-one-ℚ (succ-ℕ n@(succ-ℕ n')) _ q 1≤q =
    let
      open inequality-reasoning-Poset ℚ-Poset
      q⁰⁺ = (q , is-nonnegative-leq-ℚ⁰⁺ one-ℚ⁰⁺ q 1≤q)
    in
      chain-of-inequalities
        q
        ≤ power-ℚ n q
          by leq-power-nonzero-leq-one-ℚ n (is-nonzero-succ-ℕ n') q 1≤q
        ≤ rational-ℚ⁰⁺ (power-ℚ⁰⁺ n q⁰⁺)
          by leq-eq-ℚ (power-rational-ℚ⁰⁺ n q⁰⁺)
        ≤ rational-ℚ⁰⁺ (power-ℚ⁰⁺ n q⁰⁺) *ℚ q
          by is-inflationary-right-mul-geq-one-ℚ⁰⁺ (power-ℚ⁰⁺ n q⁰⁺) q⁰⁺ 1≤q
        ≤ power-ℚ n q *ℚ q
          by leq-eq-ℚ (ap-mul-ℚ (inv (power-rational-ℚ⁰⁺ n q⁰⁺)) refl)
```

### If `n` is odd, `q ↦ qⁿ` is cofinal and coinitial

```agda
abstract
  is-unbounded-above-power-is-odd-ℚ :
    (n : ℕ) → is-odd-ℕ n → is-cofinal-map-Poset ℚ-Poset (power-ℚ n)
  is-unbounded-above-power-is-odd-ℚ n odd-n q =
    let
      q' = max-ℚ q one-ℚ
    in
      intro-exists
        ( q')
        ( transitive-leq-ℚ
          ( q)
          ( q')
          ( power-ℚ n q')
          ( leq-power-nonzero-leq-one-ℚ
            ( n)
            ( is-nonzero-is-odd-ℕ odd-n)
            ( q')
            ( leq-right-max-ℚ q one-ℚ))
          ( leq-left-max-ℚ q one-ℚ))

  is-unbounded-below-power-is-odd-ℚ :
    (n : ℕ) → is-odd-ℕ n → is-coinitial-map-Poset ℚ-Poset (power-ℚ n)
  is-unbounded-below-power-is-odd-ℚ n odd-n q =
    map-exists _
      ( neg-ℚ)
      ( λ p pⁿ≤-q →
        binary-tr
          ( leq-ℚ)
          ( inv (power-neg-is-odd-exponent-ℚ n p odd-n))
          ( neg-neg-ℚ q)
          ( neg-leq-ℚ pⁿ≤-q))
      ( is-unbounded-above-power-is-odd-ℚ n odd-n (neg-ℚ q))
```

## See also

- [Powers of elements of a monoid](group-theory.powers-of-elements-monoids.md)
- [Powers of elements of a commutative monoid](group-theory.powers-of-elements-commutative-monoids.md)
