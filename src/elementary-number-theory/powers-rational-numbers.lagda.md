# Powers of rational numbers

```agda
module elementary-number-theory.powers-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequalities-positive-and-negative-rational-numbers
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

### For even `n`, `(-q)ⁿ = qⁿ`

```agda
abstract
  even-power-neg-ℚ :
    (n : ℕ) (q : ℚ) → is-even-ℕ n → power-ℚ n (neg-ℚ q) ＝ power-ℚ n q
  even-power-neg-ℚ _ q (k , refl) =
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
  odd-power-neg-ℚ :
    (n : ℕ) (q : ℚ) → is-odd-ℕ n → power-ℚ n (neg-ℚ q) ＝ neg-ℚ (power-ℚ n q)
  odd-power-neg-ℚ n q odd-n =
    let (k , k2+1=n) = has-odd-expansion-is-odd n odd-n
    in
      equational-reasoning
        power-ℚ n (neg-ℚ q)
        ＝ power-ℚ (succ-ℕ (k *ℕ 2)) (neg-ℚ q)
          by ap (λ m → power-ℚ m (neg-ℚ q)) (inv k2+1=n)
        ＝ power-ℚ (k *ℕ 2) (neg-ℚ q) *ℚ neg-ℚ q
          by power-succ-ℚ (k *ℕ 2) (neg-ℚ q)
        ＝ power-ℚ (k *ℕ 2) q *ℚ neg-ℚ q
          by ap-mul-ℚ (even-power-neg-ℚ _ q (k , refl)) refl
        ＝ neg-ℚ (power-ℚ (k *ℕ 2) q *ℚ q)
          by right-negative-law-mul-ℚ _ _
        ＝ neg-ℚ (power-ℚ (succ-ℕ (k *ℕ 2)) q)
          by ap neg-ℚ (inv (power-succ-ℚ (k *ℕ 2) q))
        ＝ neg-ℚ (power-ℚ n q)
          by ap (λ m → neg-ℚ (power-ℚ m q)) k2+1=n
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

### If `|p| ≤ |q|`, `|pⁿ| ≤ |qⁿ|`

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
  preserves-leq-odd-power-ℚ :
    (n : ℕ) (p q : ℚ) → is-odd-ℕ n → leq-ℚ p q →
    leq-ℚ (power-ℚ n p) (power-ℚ n q)
  preserves-leq-odd-power-ℚ n p q odd-n p≤q =
    let
      neg-pow-n r⁻ =
        let
          r = rational-ℚ⁻ r⁻
        in
          equational-reasoning
            neg-ℚ (rational-ℚ⁺ (power-ℚ⁺ n (neg-ℚ⁻ r⁻)))
            ＝ neg-ℚ (power-ℚ n (neg-ℚ r))
              by ap neg-ℚ (inv (power-rational-ℚ⁺ n (neg-ℚ⁻ r⁻)))
            ＝ neg-ℚ (neg-ℚ (power-ℚ n r))
              by ap neg-ℚ (odd-power-neg-ℚ n r odd-n)
            ＝ power-ℚ n r
              by neg-neg-ℚ _
    in
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
                  ( neg-pow-n p⁻)
                  ( neg-pow-n q⁻)
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
                    is-negative-odd-power-ℚ⁻ n (p , is-neg-p) odd-n)
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
  preserves-le-odd-power-ℚ :
    (n : ℕ) (p q : ℚ) → is-odd-ℕ n → le-ℚ p q →
    le-ℚ (power-ℚ n p) (power-ℚ n q)
  preserves-le-odd-power-ℚ n p q odd-n p<q =
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
                ( equational-reasoning
                  neg-ℚ (rational-ℚ⁺ (power-ℚ⁺ n (neg-ℚ⁻ p⁻)))
                  ＝ neg-ℚ (power-ℚ n (neg-ℚ p))
                    by ap neg-ℚ (inv (power-rational-ℚ⁺ n (neg-ℚ⁻ p⁻)))
                  ＝ neg-ℚ (neg-ℚ (power-ℚ n p))
                    by ap neg-ℚ (odd-power-neg-ℚ n p odd-n)
                  ＝ power-ℚ n p
                    by neg-neg-ℚ _)
                ( equational-reasoning
                  neg-ℚ (rational-ℚ⁺ (power-ℚ⁺ n (neg-ℚ⁻ q⁻)))
                  ＝ neg-ℚ (power-ℚ n (neg-ℚ q))
                    by ap neg-ℚ (inv (power-rational-ℚ⁺ n (neg-ℚ⁻ q⁻)))
                  ＝ neg-ℚ (neg-ℚ (power-ℚ n q))
                    by ap neg-ℚ (odd-power-neg-ℚ n q odd-n)
                  ＝ power-ℚ n q
                    by neg-neg-ℚ _)
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
                ( power-ℚ n p , is-negative-odd-power-ℚ⁻ n (p , is-neg-p) odd-n)
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

## See also

- [Powers of elements of a monoid](group-theory.powers-of-elements-monoids.md)
- [Powers of elements of a commutative monoid](group-theory.powers-of-elements-commutative-monoids.md)
