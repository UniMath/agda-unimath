# Geometric sequences of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.geometric-sequences-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.convergent-series-metric-abelian-groups
open import analysis.series-metric-abelian-groups

open import commutative-algebra.geometric-sequences-commutative-rings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings

open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.metric-additive-group-of-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.powers-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-transport
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.groups

open import lists.sequences

open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

A
{{#concept "geometric sequence" Disambiguation="of rational numbers" Agda=geometric-sequence-ℚ}}
of [rational numbers](elementary-number-theory.positive-rational-numbers.md) is
a
[geometric sequence](commutative-algebra.geometric-sequences-commutative-rings.md)
in the
[commutative ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md).

## Definitions

```agda
geometric-sequence-ℚ : UU lzero
geometric-sequence-ℚ = geometric-sequence-Commutative-Ring commutative-ring-ℚ

seq-geometric-sequence-ℚ : geometric-sequence-ℚ → sequence ℚ
seq-geometric-sequence-ℚ =
  seq-geometric-sequence-Commutative-Ring commutative-ring-ℚ

standard-geometric-sequence-ℚ : ℚ → ℚ → geometric-sequence-ℚ
standard-geometric-sequence-ℚ =
  standard-geometric-sequence-Commutative-Ring commutative-ring-ℚ

seq-standard-geometric-sequence-ℚ : ℚ → ℚ → sequence ℚ
seq-standard-geometric-sequence-ℚ =
  seq-standard-geometric-sequence-Commutative-Ring commutative-ring-ℚ
```

## Properties

### The nth term of a geometric sequence with initial term `a` and common ratio `r` is `a * rⁿ`

```agda
module _
  (a r : ℚ)
  where

  compute-standard-geometric-sequence-ℚ :
    (n : ℕ) → seq-standard-geometric-sequence-ℚ a r n ＝ a *ℚ power-ℚ n r
  compute-standard-geometric-sequence-ℚ n =
    inv
      ( htpy-mul-pow-standard-geometric-sequence-Commutative-Ring
        ( commutative-ring-ℚ)
        ( a)
        ( r)
        ( n))
```

### If `r ≠ 1`, the sum of the first `n` elements of the standard geometric sequence `n ↦ arⁿ` is `a(1-rⁿ)/(1-r)`

```agda
sum-standard-geometric-fin-sequence-ℚ : ℚ → ℚ → ℕ → ℚ
sum-standard-geometric-fin-sequence-ℚ =
  sum-standard-geometric-fin-sequence-Commutative-Ring commutative-ring-ℚ

module _
  (a r : ℚ) (r≠1 : r ≠ one-ℚ)
  where

  abstract
    compute-sum-standard-geometric-fin-sequence-ℚ :
      (n : ℕ) →
      sum-standard-geometric-fin-sequence-ℚ a r n ＝
      ( (a *ℚ rational-inv-ℚˣ (invertible-diff-neq-ℚ r one-ℚ r≠1)) *ℚ
        (one-ℚ -ℚ power-ℚ n r))
    compute-sum-standard-geometric-fin-sequence-ℚ =
      compute-sum-standard-geometric-fin-sequence-Commutative-Ring
        ( commutative-ring-ℚ)
        ( a)
        ( r)
        ( pr2 (invertible-diff-neq-ℚ r one-ℚ r≠1))
```

### If `|r| < 1`, the sum of the standard geometric sequence `n ↦ arⁿ` is `a/(1-r)`

```agda
module _
  (a r : ℚ)
  where

  standard-geometric-series-ℚ : series-Metric-Ab metric-ab-add-ℚ
  standard-geometric-series-ℚ =
    series-terms-Metric-Ab (seq-standard-geometric-sequence-ℚ a r)

  abstract
    sum-standard-geometric-sequence-ℚ :
      (|r|<1 : le-ℚ (rational-abs-ℚ r) one-ℚ) →
      is-sum-series-Metric-Ab
        ( standard-geometric-series-ℚ)
        ( a *ℚ rational-inv-ℚˣ (invertible-diff-le-abs-ℚ r one-ℚ⁺ |r|<1))
    sum-standard-geometric-sequence-ℚ |r|<1 =
      let
        r≠1 =
          nonequal-map
            ( rational-abs-ℚ)
            ( inv-tr
              ( rational-abs-ℚ r ≠_)
              ( rational-abs-rational-ℚ⁺ one-ℚ⁺)
              ( nonequal-le-ℚ |r|<1))
      in
        binary-tr
          ( is-limit-sequence-Metric-Space metric-space-ℚ)
          ( inv
            ( eq-htpy (compute-sum-standard-geometric-fin-sequence-ℚ a r r≠1)))
          ( equational-reasoning
            a *ℚ rational-inv-ℚˣ (invertible-diff-neq-ℚ r one-ℚ r≠1) *ℚ
            (one-ℚ -ℚ zero-ℚ)
            ＝
              a *ℚ rational-inv-ℚˣ (invertible-diff-neq-ℚ r one-ℚ r≠1) *ℚ one-ℚ
              by ap-mul-ℚ refl (right-zero-law-diff-ℚ _)
            ＝
              a *ℚ rational-inv-ℚˣ (invertible-diff-neq-ℚ r one-ℚ r≠1)
              by right-unit-law-mul-ℚ _)
          ( uniformly-continuous-map-limit-sequence-Metric-Space
            ( metric-space-ℚ)
            ( metric-space-ℚ)
            ( comp-uniformly-continuous-function-Metric-Space
              ( metric-space-ℚ)
              ( metric-space-ℚ)
              ( metric-space-ℚ)
              ( uniformly-continuous-left-mul-ℚ
                ( a *ℚ rational-inv-ℚˣ (invertible-diff-neq-ℚ r one-ℚ r≠1)))
              ( uniformly-continuous-diff-ℚ one-ℚ))
            ( λ n → power-ℚ n r)
            ( zero-ℚ)
            ( is-zero-limit-power-le-one-abs-ℚ r |r|<1))
```

## External links

- [Geometric progressions](https://en.wikipedia.org/wiki/Geometric_progression)
  at Wikipedia
