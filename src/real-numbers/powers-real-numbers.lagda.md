# Powers of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.powers-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.powers-of-elements-large-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.powers-positive-rational-numbers
open import elementary-number-theory.powers-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.pointwise-continuous-maps-metric-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.cofinal-and-coinitial-endomaps-real-numbers
open import real-numbers.cofinal-and-coinitial-strictly-increasing-pointwise-epsilon-delta-continuous-endomaps-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.large-ring-of-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-positive-and-negative-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.pointwise-continuous-endomaps-real-numbers
open import real-numbers.pointwise-epsilon-delta-continuous-endomaps-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-sequences-approximating-zero
open import real-numbers.similarity-real-numbers
open import real-numbers.squares-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-increasing-endomaps-real-numbers
open import real-numbers.strictly-increasing-pointwise-epsilon-delta-continuous-endomaps-real-numbers
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising a real number to a natural number power" Agda=power-ℝ}}
on the [real numbers](real-numbers.dedekind-real-numbers.md) `n x ↦ xⁿ`, is
defined by [iteratively](foundation.iterating-functions.md)
[multiplying](real-numbers.multiplication-real-numbers.md) `x` with itself `n`
times.

Note that this operation defines`0⁰` to be the empty product, `1`.

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

### For nonzero `n`, `0ⁿ = 0`

```agda
abstract
  power-nonzero-zero-ℝ : (n : ℕ⁺) → power-ℝ (nat-ℕ⁺ n) zero-ℝ ＝ zero-ℝ
  power-nonzero-zero-ℝ =
    power-nonzero-zero-Large-Commutative-Ring large-commutative-ring-ℝ
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

  power-mul-ℝ' :
    {l : Level} (m n : ℕ) {x : ℝ l} →
    power-ℝ (m *ℕ n) x ＝ power-ℝ m (power-ℝ n x)
  power-mul-ℝ' m n {x = x} =
    equational-reasoning
      power-ℝ (m *ℕ n) x
      ＝ power-ℝ (n *ℕ m) x
        by ap (λ k → power-ℝ k x) (commutative-mul-ℕ m n)
      ＝ power-ℝ m (power-ℝ n x)
        by power-mul-ℝ n m
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

### Even powers of real numbers are nonnegative

```agda
abstract
  is-nonnegative-even-power-ℝ :
    {l : Level} (n : ℕ) (x : ℝ l) → is-even-ℕ n → is-nonnegative-ℝ (power-ℝ n x)
  is-nonnegative-even-power-ℝ _ x (k , refl) =
    inv-tr
      ( is-nonnegative-ℝ)
      ( power-mul-ℝ k 2)
      ( is-nonnegative-square-ℝ (power-ℝ k x))

nonnegative-even-power-ℝ : {l : Level} (n : ℕ) (x : ℝ l) → is-even-ℕ n → ℝ⁰⁺ l
nonnegative-even-power-ℝ n x even-n =
  ( power-ℝ n x , is-nonnegative-even-power-ℝ n x even-n)
```

### For even `n`, `(-x)ⁿ ＝ xⁿ`

```agda
abstract
  power-neg-is-even-exponent-ℝ :
    {l : Level} (n : ℕ) (x : ℝ l) → is-even-ℕ n →
    power-ℝ n (neg-ℝ x) ＝ power-ℝ n x
  power-neg-is-even-exponent-ℝ _ x (k , refl) =
    equational-reasoning
      power-ℝ (k *ℕ 2) (neg-ℝ x)
      ＝ power-ℝ k (square-ℝ (neg-ℝ x))
        by power-mul-ℝ' k 2
      ＝ power-ℝ k (square-ℝ x)
        by ap (power-ℝ k) (square-neg-ℝ x)
      ＝ power-ℝ (k *ℕ 2) x
        by inv (power-mul-ℝ' k 2)
```

### For odd `n`, `(-x)ⁿ = -(xⁿ)`

```agda
abstract
  power-neg-is-odd-exponent-ℝ :
    {l : Level} (n : ℕ) (x : ℝ l) → is-odd-ℕ n →
    power-ℝ n (neg-ℝ x) ＝ neg-ℝ (power-ℝ n x)
  power-neg-is-odd-exponent-ℝ n x odd-n =
    let (k , k2+1=n) = has-odd-expansion-is-odd n odd-n
    in
      equational-reasoning
        power-ℝ n (neg-ℝ x)
        ＝ power-ℝ (succ-ℕ (k *ℕ 2)) (neg-ℝ x)
          by ap (λ m → power-ℝ m (neg-ℝ x)) (inv k2+1=n)
        ＝ power-ℝ (k *ℕ 2) (neg-ℝ x) *ℝ neg-ℝ x
          by power-succ-ℝ _ _
        ＝ power-ℝ (k *ℕ 2) x *ℝ neg-ℝ x
          by ap-mul-ℝ (power-neg-is-even-exponent-ℝ _ x (k , refl)) refl
        ＝ neg-ℝ (power-ℝ (k *ℕ 2) x *ℝ x)
          by right-negative-law-mul-ℝ _ _
        ＝ neg-ℝ (power-ℝ (succ-ℕ (k *ℕ 2)) x)
          by ap neg-ℝ (inv (power-succ-ℝ _ _))
        ＝ neg-ℝ (power-ℝ n x)
          by ap neg-ℝ (ap (λ m → power-ℝ m x) k2+1=n)
```

### `|x|ⁿ = |xⁿ|`

```agda
abstract
  power-abs-ℝ :
    {l : Level} (n : ℕ) (x : ℝ l) → power-ℝ n (abs-ℝ x) ＝ abs-ℝ (power-ℝ n x)
  power-abs-ℝ 0 x = inv (abs-real-ℝ⁺ (raise-ℝ⁺ _ one-ℝ⁺))
  power-abs-ℝ (succ-ℕ n) x =
    equational-reasoning
      power-ℝ (succ-ℕ n) (abs-ℝ x)
      ＝ power-ℝ n (abs-ℝ x) *ℝ abs-ℝ x
        by power-succ-ℝ _ _
      ＝ abs-ℝ (power-ℝ n x) *ℝ abs-ℝ x
        by ap-mul-ℝ (power-abs-ℝ n x) refl
      ＝ abs-ℝ (power-ℝ n x *ℝ x)
        by inv (abs-mul-ℝ _ _)
      ＝ abs-ℝ (power-ℝ (succ-ℕ n) x)
        by ap abs-ℝ (inv (power-succ-ℝ n x))
```

### If `|p| ≤ |q|`, `|pⁿ| ≤ |qⁿ|`

```agda
abstract
  preserves-leq-abs-power-ℝ :
    {l1 l2 : Level} (n : ℕ) (x : ℝ l1) (y : ℝ l2) → leq-ℝ (abs-ℝ x) (abs-ℝ y) →
    leq-ℝ (abs-ℝ (power-ℝ n x)) (abs-ℝ (power-ℝ n y))
  preserves-leq-abs-power-ℝ 0 _ _ _ =
    preserves-leq-sim-ℝ
      ( inv-tr
        ( sim-ℝ one-ℝ)
        ( abs-real-ℝ⁺ (raise-ℝ⁺ _ one-ℝ⁺))
        ( sim-raise-ℝ _ one-ℝ))
      ( inv-tr
        ( sim-ℝ one-ℝ)
        ( abs-real-ℝ⁺ (raise-ℝ⁺ _ one-ℝ⁺))
        ( sim-raise-ℝ _ one-ℝ))
      ( refl-leq-ℝ one-ℝ)
  preserves-leq-abs-power-ℝ (succ-ℕ n) x y |x|≤|y| =
    let
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in
    chain-of-inequalities
      abs-ℝ (power-ℝ (succ-ℕ n) x)
      ≤ abs-ℝ (power-ℝ n x *ℝ x)
        by leq-eq-ℝ (ap abs-ℝ (power-succ-ℝ n x))
      ≤ abs-ℝ (power-ℝ n x) *ℝ abs-ℝ x
        by leq-eq-ℝ (abs-mul-ℝ _ _)
      ≤ abs-ℝ (power-ℝ n y) *ℝ abs-ℝ y
        by
          preserves-leq-mul-ℝ⁰⁺
            ( nonnegative-abs-ℝ (power-ℝ n x))
            ( nonnegative-abs-ℝ (power-ℝ n y))
            ( nonnegative-abs-ℝ x)
            ( nonnegative-abs-ℝ y)
            ( preserves-leq-abs-power-ℝ n x y |x|≤|y|)
            ( |x|≤|y|)
      ≤ abs-ℝ (power-ℝ n y *ℝ y)
        by leq-eq-ℝ (inv (abs-mul-ℝ _ _))
      ≤ abs-ℝ (power-ℝ (succ-ℕ n) y)
        by leq-eq-ℝ (ap abs-ℝ (inv (power-succ-ℝ n y)))
```

### The power operation preserves similarity

```agda
abstract
  preserves-sim-power-ℝ :
    {l1 l2 : Level} (n : ℕ) {x : ℝ l1} {y : ℝ l2} → sim-ℝ x y →
    sim-ℝ (power-ℝ n x) (power-ℝ n y)
  preserves-sim-power-ℝ {l1} {l2} 0 _ =
    sim-raise-raise-ℝ l1 l2 one-ℝ
  preserves-sim-power-ℝ 1 x~y = x~y
  preserves-sim-power-ℝ (succ-ℕ n@(succ-ℕ _)) x~y =
    preserves-sim-mul-ℝ (preserves-sim-power-ℝ n x~y) x~y

  power-raise-ℝ :
    {l1 : Level} (l2 : Level) (n : ℕ) (x : ℝ l1) →
    power-ℝ n (raise-ℝ l2 x) ＝ raise-ℝ l2 (power-ℝ n x)
  power-raise-ℝ l n x =
    eq-sim-ℝ
      ( transitive-sim-ℝ _ _ _
        ( sim-raise-ℝ l _)
        ( preserves-sim-power-ℝ n (sim-raise-ℝ' l x)))
```

### For any `n`, `x ↦ xⁿ` is pointwise continuous

```agda
abstract
  is-pointwise-continuous-power-ℝ :
    (l : Level) (n : ℕ) →
    is-pointwise-continuous-endomap-ℝ (power-ℝ {l} n)
  is-pointwise-continuous-power-ℝ l 0 =
    is-pointwise-continuous-endomap-const-ℝ l (raise-one-ℝ l)
  is-pointwise-continuous-power-ℝ l 1 =
    is-pointwise-continuous-endomap-id-ℝ l
  is-pointwise-continuous-power-ℝ l (succ-ℕ n@(succ-ℕ _)) =
    is-pointwise-continuous-map-comp-pointwise-continuous-map-Metric-Space
      ( metric-space-ℝ l)
      ( product-Metric-Space (metric-space-ℝ l) (metric-space-ℝ l))
      ( metric-space-ℝ l)
      ( pointwise-continuous-map-mul-pair-ℝ l l)
      ( comp-pointwise-continuous-map-Metric-Space
        ( metric-space-ℝ l)
        ( product-Metric-Space (metric-space-ℝ l) (metric-space-ℝ l))
        ( product-Metric-Space (metric-space-ℝ l) (metric-space-ℝ l))
        ( pointwise-continuous-map-product-Metric-Space _ _ _ _
          ( power-ℝ n , is-pointwise-continuous-power-ℝ l n)
          ( pointwise-continuous-endomap-id-ℝ l))
        ( pointwise-continuous-map-isometry-Metric-Space _ _
          ( diagonal-product-isometry-Metric-Space (metric-space-ℝ l))))

pointwise-continuous-power-ℝ :
  (l : Level) (n : ℕ) → pointwise-continuous-endomap-ℝ l l
pointwise-continuous-power-ℝ l n =
  ( power-ℝ n , is-pointwise-continuous-power-ℝ l n)

abstract
  is-pointwise-ε-δ-continuous-power-ℝ :
    (l : Level) (n : ℕ) →
    is-pointwise-ε-δ-continuous-endomap-ℝ (power-ℝ {l} n)
  is-pointwise-ε-δ-continuous-power-ℝ l n =
    is-pointwise-ε-δ-continuous-map-pointwise-continuous-endomap-ℝ
      ( pointwise-continuous-power-ℝ l n)

pointwise-ε-δ-continuous-power-ℝ :
  (l : Level) (n : ℕ) → pointwise-ε-δ-continuous-endomap-ℝ l l
pointwise-ε-δ-continuous-power-ℝ l n =
  ( power-ℝ n , is-pointwise-ε-δ-continuous-power-ℝ l n)
```

### For rational `q`, `real-ℚ (power-ℚ n q)` is similar to `power-ℝ n (raise-real-ℚ l q)`

```agda
abstract
  sim-power-raise-real-ℚ :
    (l : Level) (n : ℕ) (q : ℚ) →
    sim-ℝ (real-ℚ (power-ℚ n q)) (power-ℝ n (raise-real-ℚ l q))
  sim-power-raise-real-ℚ l n q =
    concat-eq-sim-ℝ
      ( inv (power-real-ℚ n q))
      ( preserves-sim-power-ℝ n (sim-raise-ℝ l (real-ℚ q)))
```

### For odd `n`, `x ↦ xⁿ` is strictly increasing

```agda
abstract
  is-strictly-increasing-power-is-odd-exponent-ℝ :
    (l : Level) (n : ℕ) → is-odd-ℕ n →
    is-strictly-increasing-endomap-ℝ (power-ℝ {l} n)
  is-strictly-increasing-power-is-odd-exponent-ℝ l n odd-n =
    is-strictly-increasing-is-strictly-increasing-rational-pointwise-ε-δ-continuous-endomap-ℝ
      ( pointwise-ε-δ-continuous-power-ℝ l n)
      ( λ p q p<q →
        preserves-le-sim-ℝ
          ( sim-power-raise-real-ℚ l n p)
          ( sim-power-raise-real-ℚ l n q)
          ( preserves-le-real-ℚ
            ( preserves-le-power-is-odd-exponent-ℚ n p q odd-n p<q)))
```

### For odd `n`, `x ↦ xⁿ` is injective

```agda
abstract
  is-injective-power-is-odd-exponent-ℝ :
    (l : Level) (n : ℕ) → is-odd-ℕ n →
    is-injective (power-ℝ {l} n)
  is-injective-power-is-odd-exponent-ℝ l n odd-n =
    is-injective-is-strictly-increasing-endomap-ℝ
      ( power-ℝ n)
      ( is-strictly-increasing-power-is-odd-exponent-ℝ l n odd-n)
```

### For odd `n`, `x ↦ xⁿ` is cofinal and coinitial

```agda
abstract
  is-cofinal-power-is-odd-exponent-ℝ :
    (l : Level) (n : ℕ) → is-odd-ℕ n →
    is-cofinal-endomap-ℝ (power-ℝ {l} n)
  is-cofinal-power-is-odd-exponent-ℝ l n odd-n q =
    map-exists _
      ( raise-real-ℚ l)
      ( λ p q≤pⁿ →
        preserves-leq-right-sim-ℝ
          ( sim-power-raise-real-ℚ l n p)
          ( preserves-leq-real-ℚ q≤pⁿ))
      ( is-cofinal-power-is-odd-ℚ n odd-n q)

  is-coinitial-power-is-odd-exponent-ℝ :
    (l : Level) (n : ℕ) → is-odd-ℕ n →
    is-coinitial-endomap-ℝ (power-ℝ {l} n)
  is-coinitial-power-is-odd-exponent-ℝ l n odd-n q =
    map-exists _
      ( raise-real-ℚ l)
      ( λ p pⁿ≤q →
        preserves-leq-left-sim-ℝ
          ( sim-power-raise-real-ℚ l n p)
          ( preserves-leq-real-ℚ pⁿ≤q))
      ( is-coinitial-power-is-odd-ℚ n odd-n q)
```
