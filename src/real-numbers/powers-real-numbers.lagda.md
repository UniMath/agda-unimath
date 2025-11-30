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
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.powers-positive-rational-numbers
open import elementary-number-theory.powers-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.large-ring-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-positive-and-negative-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-sequences-approximating-zero
open import real-numbers.similarity-real-numbers
open import real-numbers.squares-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-monotonic-functions-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.pointwise-continuous-functions-metric-spaces
open import real-numbers.pointwise-continuous-functions-real-numbers
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

### The power operation preserves similarity

```agda
abstract
  preserves-sim-power-ℝ :
    {l1 l2 : Level} (n : ℕ) {x : ℝ l1} {y : ℝ l2} → sim-ℝ x y →
    sim-ℝ (power-ℝ n x) (power-ℝ n y)
  preserves-sim-power-ℝ n =
    preserves-sim-power-Large-Commutative-Ring large-commutative-ring-ℝ n _ _
```

### The power operation commutes with raising universe level

```agda
abstract
  power-raise-ℝ :
    {l0 : Level} (l : Level) (n : ℕ) (x : ℝ l0) →
    power-ℝ n (raise-ℝ l x) ＝ raise-ℝ l (power-ℝ n x)
  power-raise-ℝ l n x =
    eq-sim-ℝ
      ( similarity-reasoning-ℝ
        power-ℝ n (raise-ℝ l x)
        ~ℝ power-ℝ n x
          by preserves-sim-power-ℝ n (sim-raise-ℝ' l x)
        ~ℝ raise-ℝ l (power-ℝ n x)
          by sim-raise-ℝ l _)
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

### Powers of positive real numbers are positive

```agda
abstract
  is-positive-power-ℝ⁺ :
    {l : Level} (n : ℕ) (x : ℝ⁺ l) → is-positive-ℝ (power-ℝ n (real-ℝ⁺ x))
  is-positive-power-ℝ⁺ 0 _ =
    is-positive-sim-ℝ (sim-raise-ℝ _ _) (is-positive-real-ℝ⁺ one-ℝ⁺)
  is-positive-power-ℝ⁺ 1 (_ , is-pos-x) = is-pos-x
  is-positive-power-ℝ⁺ (succ-ℕ n@(succ-ℕ _)) x⁺@(x , is-pos-x) =
    is-positive-mul-ℝ (is-positive-power-ℝ⁺ n x⁺) is-pos-x

power-ℝ⁺ : {l : Level} → ℕ → ℝ⁺ l → ℝ⁺ l
power-ℝ⁺ n x⁺@(x , _) = (power-ℝ n x , is-positive-power-ℝ⁺ n x⁺)
```

### Powers of nonnegative real numbers are nonnegative

```agda
abstract
  is-nonnegative-power-ℝ⁰⁺ :
    {l : Level} (n : ℕ) (x : ℝ⁰⁺ l) → is-nonnegative-ℝ (power-ℝ n (real-ℝ⁰⁺ x))
  is-nonnegative-power-ℝ⁰⁺ {l} 0 _ =
    is-nonnegative-real-ℝ⁰⁺ (raise-ℝ⁰⁺ l one-ℝ⁰⁺)
  is-nonnegative-power-ℝ⁰⁺ 1 (x , is-nonneg-x) = is-nonneg-x
  is-nonnegative-power-ℝ⁰⁺ (succ-ℕ n@(succ-ℕ _)) x⁰⁺@(x , is-nonneg-x) =
    is-nonnegative-mul-ℝ
      ( is-nonnegative-power-ℝ⁰⁺ n x⁰⁺)
      ( is-nonneg-x)

power-ℝ⁰⁺ : {l : Level} → ℕ → ℝ⁰⁺ l → ℝ⁰⁺ l
power-ℝ⁰⁺ n x⁰⁺@(x , _) = (power-ℝ n x , is-nonnegative-power-ℝ⁰⁺ n x⁰⁺)
```

### Even powers of negative real numbers are positive

```agda
abstract
  is-positive-even-power-ℝ⁻ :
    {l : Level} (n : ℕ) (x : ℝ⁻ l) → is-even-ℕ n →
    is-positive-ℝ (power-ℝ n (real-ℝ⁻ x))
  is-positive-even-power-ℝ⁻ _ x (k , refl) =
    inv-tr
      ( is-positive-ℝ)
      ( power-mul-ℝ' k 2)
      ( is-positive-power-ℝ⁺ k (square-ℝ⁻ x))
```

### Odd powers of negative real numbers are negative

```agda
abstract
  is-negative-odd-power-ℝ⁻ :
    {l : Level} (n : ℕ) (x : ℝ⁻ l) → is-odd-ℕ n →
    is-negative-ℝ (power-ℝ n (real-ℝ⁻ x))
  is-negative-odd-power-ℝ⁻ n x⁻@(x , is-neg-x) odd-n =
    let (k , k2+1=n) = has-odd-expansion-is-odd n odd-n
    in
      tr
        ( is-negative-ℝ)
        ( equational-reasoning
          power-ℝ (k *ℕ 2) x *ℝ x
          ＝ power-ℝ (succ-ℕ (k *ℕ 2)) x
            by inv (power-succ-ℝ _ _)
          ＝ power-ℝ n x
            by ap (λ m → power-ℝ m x) k2+1=n)
        ( is-negative-mul-positive-negative-ℝ
          ( is-positive-even-power-ℝ⁻ _ x⁻ (k , refl))
          ( is-neg-x))
```

### For even `n`, `(-x)ⁿ ＝ xⁿ`

```agda
abstract
  even-power-neg-ℝ :
    {l : Level} (n : ℕ) (x : ℝ l) → is-even-ℕ n →
    power-ℝ n (neg-ℝ x) ＝ power-ℝ n x
  even-power-neg-ℝ _ x (k , refl) =
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
  odd-power-neg-ℝ :
    {l : Level} (n : ℕ) (x : ℝ l) → is-odd-ℕ n →
    power-ℝ n (neg-ℝ x) ＝ neg-ℝ (power-ℝ n x)
  odd-power-neg-ℝ n x odd-n =
    let (k , k2+1=n) = has-odd-expansion-is-odd n odd-n
    in
      equational-reasoning
        power-ℝ n (neg-ℝ x)
        ＝ power-ℝ (succ-ℕ (k *ℕ 2)) (neg-ℝ x)
          by ap (λ m → power-ℝ m (neg-ℝ x)) (inv k2+1=n)
        ＝ power-ℝ (k *ℕ 2) (neg-ℝ x) *ℝ neg-ℝ x
          by power-succ-ℝ _ _
        ＝ power-ℝ (k *ℕ 2) x *ℝ neg-ℝ x
          by ap-mul-ℝ (even-power-neg-ℝ _ x (k , refl)) refl
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

### If `x` and `y` are nonnegative such that `x ≤ y`, then `xⁿ ≤ yⁿ`

```agda
abstract
  preserves-leq-power-real-ℝ⁰⁺ :
    {l1 l2 : Level} (n : ℕ) (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) → leq-ℝ⁰⁺ x y →
    leq-ℝ (power-ℝ n (real-ℝ⁰⁺ x)) (power-ℝ n (real-ℝ⁰⁺ y))
  preserves-leq-power-real-ℝ⁰⁺ {l1} {l2} 0 _ _ _ =
    leq-sim-ℝ
      ( transitive-sim-ℝ _ one-ℝ _
        ( sim-raise-ℝ l2 one-ℝ)
        ( symmetric-sim-ℝ (sim-raise-ℝ l1 one-ℝ)))
  preserves-leq-power-real-ℝ⁰⁺ (succ-ℕ n) x⁰⁺@(x , _) y⁰⁺@(y , _) x≤y =
    let
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in
      chain-of-inequalities
      power-ℝ (succ-ℕ n) x
      ≤ power-ℝ n x *ℝ x
        by leq-eq-ℝ (power-succ-ℝ n x)
      ≤ power-ℝ n y *ℝ y
        by
          preserves-leq-mul-ℝ⁰⁺
            ( power-ℝ⁰⁺ n x⁰⁺)
            ( power-ℝ⁰⁺ n y⁰⁺)
            ( x⁰⁺)
            ( y⁰⁺)
            ( preserves-leq-power-real-ℝ⁰⁺ n x⁰⁺ y⁰⁺ x≤y)
            ( x≤y)
      ≤ power-ℝ (succ-ℕ n) y
        by leq-eq-ℝ (inv (power-succ-ℝ n y))
```

### If `|r| < 1`, then `rⁿ` approaches 0

```agda
abstract
  is-zero-lim-power-le-one-abs-ℝ :
    {l : Level} (r : ℝ l) → le-ℝ (abs-ℝ r) one-ℝ →
    is-zero-limit-sequence-ℝ (λ n → power-ℝ n r)
  is-zero-lim-power-le-one-abs-ℝ r |r|<1 =
    let
      open
        do-syntax-trunc-Prop (is-zero-limit-prop-sequence-ℝ (λ n → power-ℝ n r))
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in do
      (ε , |r|<ε , ε<1ℝ) ← dense-rational-le-ℝ _ _ |r|<1
      let
        is-pos-ε =
          reflects-is-positive-real-ℚ
            ( is-positive-le-ℝ⁰⁺ (nonnegative-abs-ℝ r) (real-ℚ ε) |r|<ε)
        ε⁺ = (ε , is-pos-ε)
      is-zero-limit-sequence-leq-abs-rational-zero-limit-sequence-ℝ
        ( λ n → power-ℝ n r)
        ( (λ n → rational-ℚ⁺ (power-ℚ⁺ n ε⁺)) ,
          is-zero-limit-power-le-one-ℚ⁺ ε⁺ (reflects-le-real-ℚ ε<1ℝ))
        ( λ n →
          chain-of-inequalities
            abs-ℝ (power-ℝ n r)
            ≤ abs-ℝ (power-ℝ n (real-ℚ ε))
              by
                preserves-leq-abs-power-ℝ
                  ( n)
                  ( r)
                  ( real-ℚ ε)
                  ( inv-tr
                    ( leq-ℝ (abs-ℝ r))
                    ( abs-real-ℝ⁺ (positive-real-ℚ⁺ ε⁺))
                    ( leq-le-ℝ |r|<ε))
            ≤ power-ℝ n (real-ℚ ε)
              by leq-eq-ℝ (abs-real-ℝ⁺ (power-ℝ⁺ n (positive-real-ℚ⁺ ε⁺)))
            ≤ real-ℚ (power-ℚ n ε)
              by leq-eq-ℝ (power-real-ℚ n ε)
            ≤ real-ℚ⁺ (power-ℚ⁺ n ε⁺)
              by leq-eq-ℝ (ap real-ℚ (power-rational-ℚ⁺ n ε⁺)))
```

### For any `n`, `power-ℝ n` is pointwise continuous

```agda
abstract
  is-pointwise-continuous-power-ℝ :
    {l : Level} (n : ℕ) → is-pointwise-continuous-function-ℝ {l} (power-ℝ n)
  is-pointwise-continuous-power-ℝ 0 =
    is-pointwise-continuous-constant-function-Metric-Space _ _ _
  is-pointwise-continuous-power-ℝ 1 =
    is-pointwise-continuous-id-Metric-Space _
  is-pointwise-continuous-power-ℝ {l} (succ-ℕ n@(succ-ℕ _)) =
    is-pointwise-continuous-map-comp-pointwise-continuous-function-Metric-Space
      ( metric-space-ℝ l)
      ( product-Metric-Space (metric-space-ℝ l) (metric-space-ℝ l))
      ( metric-space-ℝ l)
      {! ind-Σ   !}
      {!   !}
```

### Odd powers of real numbers preserve strict inequality

```agda
abstract
  preserves-le-odd-power-ℝ :
    {l1 l2 : Level} (n : ℕ) {x : ℝ l1} {y : ℝ l2} → is-odd-ℕ n → le-ℝ x y →
    le-ℝ (power-ℝ n x) (power-ℝ n y)
  preserves-le-odd-power-ℝ {l1} {l2} n {x} {y} odd-n x<y =
    le-le-raise-ℝ
      ( l1 ⊔ l2)
      ( is-strictly-monotonic-is-strictly-monotonic-rational-ℝ
        {!   !}
        {!   !}
        {!   !}
        {!   !}
        {!   !})
```
