# The reciprocal triangular numbers

```agda
module elementary-number-theory.reciprocal-triangular-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.rational-numbers

-- open import elementary-number-theory.addition-rational-numbers
-- open import elementary-number-theory.additive-group-of-rational-numbers
-- open import elementary-number-theory.difference-rational-numbers
-- open import elementary-number-theory.divisibility-natural-numbers
-- open import elementary-number-theory.multiplication-natural-numbers
-- open import elementary-number-theory.multiplication-positive-rational-numbers
-- open import elementary-number-theory.multiplication-rational-numbers
-- open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
-- open import elementary-number-theory.natural-numbers
-- open import elementary-number-theory.nonzero-natural-numbers
-- open import elementary-number-theory.positive-rational-numbers
-- open import elementary-number-theory.rational-numbers
-- open import elementary-number-theory.semiring-of-natural-numbers
-- open import elementary-number-theory.series-rational-numbers
-- open import elementary-number-theory.unit-fractions-rational-numbers

-- open import foundation.action-on-identifications-functions
-- open import foundation.binary-transport
-- open import foundation.dependent-pair-types
-- open import foundation.function-extensionality
-- open import foundation.homotopies
-- open import foundation.identity-types

-- open import group-theory.abelian-groups
-- open import group-theory.groups

-- open import metric-spaces.limits-of-sequences-metric-spaces
-- open import metric-spaces.metric-space-of-rational-numbers
-- open import metric-spaces.rational-sequences-approximating-zero
-- open import metric-spaces.uniformly-continuous-maps-metric-spaces

-- open import ring-theory.partial-sums-sequences-semirings
```

</details>

## Idea

A
{{#concept "reciprocal triangular number" Agda=reciprocal-triangular-number-ℚ}}
is a [rational number](elementary-number-theory.rational-numbers.md) of the form

$$
\frac{1}{T_n}=\frac{2}{n(n+1)},
$$

where $T_n$ is the $n$th [triangular number](elementary-number-theory.triangular-numbers.md) for some $n>0$.

## Definitions

### Reciprocal triangular numbers

```agda
reciprocal-triangular-number-succ-ℕ : ℕ → ℚ
reciprocal-triangular-number-succ-ℕ n =
  reciprocal-rational-ℕ⁺ (nonzero-triangular-number-succ-ℕ n)

reciprocal-triangular-number-ℕ : (n : ℕ) → is-nonzero-ℕ n → ℚ
reciprocal-triangular-number-ℕ n = ?
```

### The sum of the reciprocals of the first `n` nonzero triangular numbers is `2(1-1/(n+1))`

```agda
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

series-reciprocal-triangular-number-ℕ : series-ℚ
series-reciprocal-triangular-number-ℕ =
  series-terms-ℚ reciprocal-triangular-number-succ-ℕ

abstract
  compute-partial-sum-series-reciprocal-triangular-number-ℕ :
    (n : ℕ) →
    partial-sum-series-ℚ
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
      partial-sum-series-ℚ
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
    is-sum-series-ℚ
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
      ( is-limit-map-sequence-uniformly-continuous-map-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( comp-uniformly-continuous-map-Metric-Space
          ( metric-space-ℚ)
          ( metric-space-ℚ)
          ( metric-space-ℚ)
          ( uniformly-continuous-map-left-mul-ℚ (rational-ℕ 2))
          ( uniformly-continuous-map-left-diff-ℚ one-ℚ))
        ( reciprocal-rational-succ-ℕ)
        ( zero-ℚ)
        ( is-zero-limit-reciprocal-rational-succ-ℕ))
```

