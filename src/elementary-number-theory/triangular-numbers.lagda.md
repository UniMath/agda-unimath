# The triangular numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.triangular-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.convergent-series-metric-abelian-groups
open import analysis.series-metric-abelian-groups

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.metric-additive-group-of-rational-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.semiring-of-natural-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications

open import group-theory.abelian-groups
open import group-theory.groups

open import lists.sequences

open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.rational-sequences-approximating-zero
open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import ring-theory.partial-sums-sequences-semirings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings
```

</details>

## Idea

{{#concept "Triangular numbers" WD="triangular number" WDID=Q245102 OEIS=A000217 Agda=triangular-number-ℕ}}
are the sequence of
[natural numbers](elementary-number-theory.natural-numbers.md) `Tₙ` defined by:

- `T₀ = 0`;
- `Tₙ₊₁ = Tₙ + n + 1`.

I.e., `Tₙ = Σ (k ≤ n) k`. The nth triangular number is equal to `n(n+1)/2`.

## Definition

### Triangular numbers

```agda
triangular-number-ℕ : ℕ → ℕ
triangular-number-ℕ 0 = 0
triangular-number-ℕ (succ-ℕ n) = (triangular-number-ℕ n) +ℕ (succ-ℕ n)
```

### The sums `Σ (k ≤ n) k`

```agda
sum-leq-ℕ : ℕ → ℕ
sum-leq-ℕ = seq-sum-sequence-Semiring ℕ-Semiring (λ k → k)
```

## Properties

### The nth triangular number is the sum `Σ (k ≤ n) k`

```agda
htpy-sum-leq-triangular-ℕ : triangular-number-ℕ ~ sum-leq-ℕ
htpy-sum-leq-triangular-ℕ zero-ℕ = refl
htpy-sum-leq-triangular-ℕ (succ-ℕ n) =
  ap (add-ℕ' (succ-ℕ n)) (htpy-sum-leq-triangular-ℕ n)
```

### Twice the nth triangular number is `n(n+1)`

```agda
abstract
  compute-twice-triangular-number-ℕ :
    (n : ℕ) → (triangular-number-ℕ n) +ℕ (triangular-number-ℕ n) ＝ n *ℕ succ-ℕ n
  compute-twice-triangular-number-ℕ zero-ℕ = refl
  compute-twice-triangular-number-ℕ (succ-ℕ n) =
    ( interchange-law-add-add-ℕ
      ( triangular-number-ℕ n)
      ( succ-ℕ n)
      ( triangular-number-ℕ n)
      ( succ-ℕ n)) ∙
    ( ap-add-ℕ
      ( compute-twice-triangular-number-ℕ n)
      ( inv (left-two-law-mul-ℕ (succ-ℕ n)))) ∙
    ( inv (right-distributive-mul-add-ℕ n 2 (succ-ℕ n))) ∙
    ( commutative-mul-ℕ (n +ℕ 2) (succ-ℕ n))

  compute-double-triangular-number-ℕ :
    (n : ℕ) → 2 *ℕ triangular-number-ℕ n ＝ n *ℕ succ-ℕ n
  compute-double-triangular-number-ℕ n =
    left-two-law-mul-ℕ _ ∙ compute-twice-triangular-number-ℕ n
```

### The nth triangular number is `n(n+1)/2`

```agda
module _
  (n : ℕ)
  where

  compute-triangular-number-ℕ :
    Σ ( div-ℕ 2 (n *ℕ succ-ℕ n))
      ( λ H → quotient-div-ℕ 2 (n *ℕ succ-ℕ n) H ＝ triangular-number-ℕ n)
  pr1 (pr1 compute-triangular-number-ℕ) = triangular-number-ℕ n
  pr2 (pr1 compute-triangular-number-ℕ) =
    ( right-two-law-mul-ℕ (triangular-number-ℕ n)) ∙
    ( compute-twice-triangular-number-ℕ n)
  pr2 compute-triangular-number-ℕ = refl
```

### The `n+1`th triangular number is nonzero

```agda
abstract
  is-nonzero-triangular-number-succ-ℕ :
    (n : ℕ) → is-nonzero-ℕ (triangular-number-ℕ (succ-ℕ n))
  is-nonzero-triangular-number-succ-ℕ 0 ()
  is-nonzero-triangular-number-succ-ℕ (succ-ℕ n) ()

nonzero-triangular-number-succ-ℕ : ℕ → ℕ⁺
nonzero-triangular-number-succ-ℕ n =
  ( triangular-number-ℕ (succ-ℕ n) ,
    is-nonzero-triangular-number-succ-ℕ n)
```

### The sum of the reciprocals of the first `n` nonzero triangular numbers is `2(1-1/(n+1))`

```agda
reciprocal-triangular-number-succ-ℕ : ℕ → ℚ
reciprocal-triangular-number-succ-ℕ n =
  reciprocal-rational-ℕ⁺ (nonzero-triangular-number-succ-ℕ n)

abstract
  compute-reciprocal-triangular-number-succ-ℕ :
    (n : ℕ) →
    reciprocal-triangular-number-succ-ℕ n ＝
    rational-ℕ 2 *ℚ
    reciprocal-rational-ℕ⁺ (succ-nonzero-ℕ' n *ℕ⁺ succ-nonzero-ℕ' (succ-ℕ n))
  compute-reciprocal-triangular-number-succ-ℕ n =
    ap
      ( rational-ℚ⁺)
      ( equational-reasoning
        inv-ℚ⁺ (positive-rational-ℕ⁺ (nonzero-triangular-number-succ-ℕ n))
        ＝
          two-ℚ⁺ *ℚ⁺
          ( inv-ℚ⁺ two-ℚ⁺ *ℚ⁺
            inv-ℚ⁺ (positive-rational-ℕ⁺ (nonzero-triangular-number-succ-ℕ n)))
          by
            inv
              ( is-section-left-div-Group
                ( group-mul-ℚ⁺)
                ( positive-rational-ℕ⁺ (2 , λ ()))
                ( inv-ℚ⁺
                  ( positive-rational-ℕ⁺ (nonzero-triangular-number-succ-ℕ n))))
        ＝
          two-ℚ⁺ *ℚ⁺
          ( inv-ℚ⁺
            ( two-ℚ⁺ *ℚ⁺
              positive-rational-ℕ⁺ (nonzero-triangular-number-succ-ℕ n)))
          by ap-mul-ℚ⁺ refl (inv (distributive-inv-mul-ℚ⁺ _ _))
        ＝
          two-ℚ⁺ *ℚ⁺
          ( inv-ℚ⁺
            ( positive-rational-ℕ⁺
              ( 2 *ℕ triangular-number-ℕ (succ-ℕ n) , λ ())))
          by
            ap-mul-ℚ⁺
              ( refl)
              ( ap
                ( inv-ℚ⁺)
                ( eq-ℚ⁺ (mul-rational-ℕ 2 (triangular-number-ℕ (succ-ℕ n)))))
        ＝
          two-ℚ⁺ *ℚ⁺
          positive-reciprocal-rational-ℕ⁺
            ( succ-nonzero-ℕ' n *ℕ⁺ succ-nonzero-ℕ' (succ-ℕ n))
          by
            ap-mul-ℚ⁺
              ( refl)
              ( ap
                ( positive-reciprocal-rational-ℕ⁺)
                ( eq-nonzero-ℕ
                  ( compute-double-triangular-number-ℕ (succ-ℕ n)))))

series-reciprocal-triangular-number-ℕ : series-Metric-Ab metric-ab-add-ℚ
series-reciprocal-triangular-number-ℕ =
  series-terms-Metric-Ab reciprocal-triangular-number-succ-ℕ

abstract
  compute-partial-sum-series-reciprocal-triangular-number-ℕ :
    (n : ℕ) →
    partial-sum-series-Metric-Ab
      ( metric-ab-add-ℚ)
      ( series-reciprocal-triangular-number-ℕ)
      ( n) ＝
    rational-ℕ 2 *ℚ (one-ℚ -ℚ reciprocal-rational-succ-ℕ n)
  compute-partial-sum-series-reciprocal-triangular-number-ℕ 0 =
    inv
      ( equational-reasoning
        rational-ℕ 2 *ℚ (one-ℚ -ℚ reciprocal-rational-succ-ℕ zero-ℕ)
        ＝ rational-ℕ 2 *ℚ (one-ℚ -ℚ one-ℚ)
          by ap-mul-ℚ refl (ap-diff-ℚ refl (ap rational-ℚ⁺ inv-one-ℚ⁺))
        ＝ rational-ℕ 2 *ℚ zero-ℚ
          by ap-mul-ℚ refl (right-inverse-law-add-ℚ one-ℚ)
        ＝ zero-ℚ
          by right-zero-law-mul-ℚ _)
  compute-partial-sum-series-reciprocal-triangular-number-ℕ (succ-ℕ n) =
    equational-reasoning
      partial-sum-series-Metric-Ab
        ( metric-ab-add-ℚ)
        ( series-reciprocal-triangular-number-ℕ)
        ( n) +ℚ
      reciprocal-triangular-number-succ-ℕ n
      ＝
        rational-ℕ 2 *ℚ (one-ℚ -ℚ reciprocal-rational-succ-ℕ n) +ℚ
        rational-ℕ 2 *ℚ
          reciprocal-rational-ℕ⁺
            ( succ-nonzero-ℕ' n *ℕ⁺ succ-nonzero-ℕ' (succ-ℕ n))
        by
          ap-add-ℚ
            ( compute-partial-sum-series-reciprocal-triangular-number-ℕ n)
            ( compute-reciprocal-triangular-number-succ-ℕ n)
      ＝
        rational-ℕ 2 *ℚ
        ( ( one-ℚ -ℚ reciprocal-rational-succ-ℕ n) +ℚ
          reciprocal-rational-ℕ⁺
            ( succ-nonzero-ℕ' n *ℕ⁺ succ-nonzero-ℕ' (succ-ℕ n)))
        by inv (left-distributive-mul-add-ℚ _ _ _)
      ＝
        rational-ℕ 2 *ℚ
        ( ( one-ℚ -ℚ reciprocal-rational-succ-ℕ n) +ℚ
          ( reciprocal-rational-succ-ℕ n -ℚ
            reciprocal-rational-succ-ℕ (succ-ℕ n)))
        by
          ap-mul-ℚ
            ( refl)
            ( ap-add-ℚ refl (inv (diff-succ-reciprocal-ℕ⁺ (succ-nonzero-ℕ' n))))
      ＝
        rational-ℕ 2 *ℚ
        ( one-ℚ -ℚ reciprocal-rational-succ-ℕ (succ-ℕ n))
        by ap-mul-ℚ refl (add-right-subtraction-Ab abelian-group-add-ℚ _ _ _)
```

### The sum of reciprocals of triangular numbers converges to 2

This theorem is the [42nd](literature.100-theorems.md#42) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

```agda
abstract
  sum-reciprocal-triangular-number-ℕ :
    is-sum-series-Metric-Ab
      ( metric-ab-add-ℚ)
      ( series-reciprocal-triangular-number-ℕ)
      ( rational-ℕ 2)
  sum-reciprocal-triangular-number-ℕ =
    binary-tr
      ( is-limit-sequence-Metric-Space metric-space-ℚ)
      ( inv (eq-htpy compute-partial-sum-series-reciprocal-triangular-number-ℕ))
      ( equational-reasoning
        rational-ℕ 2 *ℚ (one-ℚ -ℚ zero-ℚ)
        ＝ rational-ℕ 2 *ℚ one-ℚ
          by ap-mul-ℚ refl (right-zero-law-diff-ℚ one-ℚ)
        ＝ rational-ℕ 2
          by right-unit-law-mul-ℚ _)
      ( uniformly-continuous-map-limit-sequence-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( comp-uniformly-continuous-function-Metric-Space
          ( metric-space-ℚ)
          ( metric-space-ℚ)
          ( metric-space-ℚ)
          ( uniformly-continuous-left-mul-ℚ (rational-ℕ 2))
          ( uniformly-continuous-diff-ℚ one-ℚ))
          ( reciprocal-rational-succ-ℕ)
          ( zero-ℚ)
          ( is-zero-limit-reciprocal-rational-succ-ℕ))
```

## External references

- [Triangular number](https://en.wikipedia.org/wiki/Triangular_number) at
  Wikipedia.
- [A000217](https://oeis.org/A000217) in the OEIS
