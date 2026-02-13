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
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.metric-additive-group-of-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.powers-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.groups

open import lists.sequences

open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.uniformly-continuous-maps-metric-spaces
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
          ( is-limit-map-sequence-uniformly-continuous-map-Metric-Space
            ( metric-space-ℚ)
            ( metric-space-ℚ)
            ( comp-uniformly-continuous-map-Metric-Space
              ( metric-space-ℚ)
              ( metric-space-ℚ)
              ( metric-space-ℚ)
              ( uniformly-continuous-map-left-mul-ℚ
                ( a *ℚ rational-inv-ℚˣ (invertible-diff-neq-ℚ r one-ℚ r≠1)))
              ( uniformly-continuous-map-left-diff-ℚ one-ℚ))
            ( λ n → power-ℚ n r)
            ( zero-ℚ)
            ( is-zero-limit-power-le-one-abs-ℚ r |r|<1))
```

### The partial sums of a geometric sequence are bounded by the geometric sum

```agda
abstract
  leq-bound-sum-standard-geometric-fin-sequence-ℚ :
    (r : ℚ⁺) (b : ℚ) →
    leq-ℚ zero-ℚ b →
    leq-ℚ (one-ℚ +ℚ rational-ℚ⁺ r *ℚ b) b →
    (k : ℕ) →
    leq-ℚ (sum-standard-geometric-fin-sequence-ℚ one-ℚ (rational-ℚ⁺ r) k) b
  leq-bound-sum-standard-geometric-fin-sequence-ℚ r b zero≤b one+r*b≤b zero-ℕ =
    transitive-leq-ℚ
      ( sum-standard-geometric-fin-sequence-ℚ one-ℚ (rational-ℚ⁺ r) zero-ℕ)
      ( zero-ℚ)
      ( b)
      ( zero≤b)
      ( leq-eq-ℚ refl)
  leq-bound-sum-standard-geometric-fin-sequence-ℚ
    r b zero≤b one+r*b≤b (succ-ℕ k) =
    transitive-leq-ℚ
      ( sum-standard-geometric-fin-sequence-ℚ one-ℚ (rational-ℚ⁺ r) (succ-ℕ k))
      ( one-ℚ +ℚ
        ( rational-ℚ⁺ r *ℚ
          sum-standard-geometric-fin-sequence-ℚ one-ℚ (rational-ℚ⁺ r) k))
      ( b)
      ( transitive-leq-ℚ
        ( one-ℚ +ℚ
          ( rational-ℚ⁺ r *ℚ
            sum-standard-geometric-fin-sequence-ℚ one-ℚ (rational-ℚ⁺ r) k))
        ( one-ℚ +ℚ (rational-ℚ⁺ r *ℚ b))
        ( b)
        ( one+r*b≤b)
        ( preserves-leq-right-add-ℚ
          ( one-ℚ)
          ( rational-ℚ⁺ r *ℚ
            sum-standard-geometric-fin-sequence-ℚ one-ℚ (rational-ℚ⁺ r) k)
          ( rational-ℚ⁺ r *ℚ b)
          ( preserves-leq-left-mul-ℚ⁺
            ( r)
            ( sum-standard-geometric-fin-sequence-ℚ one-ℚ (rational-ℚ⁺ r) k)
            ( b)
            ( leq-bound-sum-standard-geometric-fin-sequence-ℚ
              r b zero≤b one+r*b≤b k))))
      ( leq-eq-ℚ
        ( compute-sum-standard-geometric-fin-sequence-succ-Commutative-Ring
          ( commutative-ring-ℚ)
          ( one-ℚ)
          ( rational-ℚ⁺ r)
          ( k)))
```

### The geometric series 1 + ½ + ¼ + ⅛ + ⋯

```agda
le-rational-one-half-one-ℚ :
  le-ℚ (rational-ℚ⁺ one-half-ℚ⁺) (rational-ℚ⁺ one-ℚ⁺)
le-rational-one-half-one-ℚ =
  tr
    ( le-ℚ (rational-ℚ⁺ one-half-ℚ⁺))
    ( ap rational-ℚ⁺ inv-one-ℚ⁺)
    ( inv-le-ℚ⁺
      ( one-ℚ⁺)
      ( two-ℚ⁺)
      ( preserves-le-rational-ℕ {1} {2} _))

le-abs-one-half-one-ℚ :
  le-ℚ (rational-abs-ℚ one-half-ℚ) (rational-ℚ⁺ one-ℚ⁺)
le-abs-one-half-one-ℚ =
  tr
    ( λ z → le-ℚ z (rational-ℚ⁺ one-ℚ⁺))
    ( inv (rational-abs-rational-ℚ⁺ one-half-ℚ⁺))
    ( le-rational-one-half-one-ℚ)

sum-standard-geometric-sequence-one-half-ℚ : ℚ
sum-standard-geometric-sequence-one-half-ℚ =
  ( one-ℚ) *ℚ
  ( rational-inv-ℚˣ
    ( invertible-diff-le-abs-ℚ one-half-ℚ one-ℚ⁺ le-abs-one-half-one-ℚ))

abstract
  is-sum-standard-geometric-sequence-one-half-ℚ :
    is-sum-series-Metric-Ab {G = metric-ab-add-ℚ}
      ( series-terms-Metric-Ab
        ( seq-standard-geometric-sequence-ℚ one-ℚ one-half-ℚ))
      ( sum-standard-geometric-sequence-one-half-ℚ)
  is-sum-standard-geometric-sequence-one-half-ℚ =
    sum-standard-geometric-sequence-ℚ one-ℚ one-half-ℚ le-abs-one-half-one-ℚ

  eq-diff-one-one-half-one-half-ℚ :
    one-ℚ -ℚ one-half-ℚ ＝ one-half-ℚ
  eq-diff-one-one-half-one-half-ℚ =
    equational-reasoning
      one-ℚ -ℚ one-half-ℚ
      ＝ (one-half-ℚ +ℚ one-half-ℚ) -ℚ one-half-ℚ
        by ap (_-ℚ one-half-ℚ) (inv twice-one-half-ℚ)
      ＝ one-half-ℚ +ℚ (one-half-ℚ -ℚ one-half-ℚ)
        by associative-add-ℚ one-half-ℚ one-half-ℚ (neg-ℚ one-half-ℚ)
      ＝ one-half-ℚ +ℚ zero-ℚ
        by ap (one-half-ℚ +ℚ_) (right-inverse-law-add-ℚ one-half-ℚ)
      ＝ one-half-ℚ
        by right-unit-law-add-ℚ one-half-ℚ

  eq-sum-standard-geometric-sequence-one-half-rational-two-ℚ :
    sum-standard-geometric-sequence-one-half-ℚ ＝ rational-ℕ 2
  eq-sum-standard-geometric-sequence-one-half-rational-two-ℚ =
    let
      q-one-half-ℚˣ : ℚˣ
      q-one-half-ℚˣ =
        invertible-diff-le-abs-ℚ one-half-ℚ one-ℚ⁺ le-abs-one-half-one-ℚ

      eq-rational-q-one-half-ℚˣ :
        rational-ℚˣ q-one-half-ℚˣ ＝ one-ℚ -ℚ one-half-ℚ
      eq-rational-q-one-half-ℚˣ = refl

      eq-mul-two-rational-q-one-half-ℚˣ :
        rational-ℕ 2 *ℚ rational-ℚˣ q-one-half-ℚˣ ＝ one-ℚ
      eq-mul-two-rational-q-one-half-ℚˣ =
        ( ap (rational-ℕ 2 *ℚ_) eq-rational-q-one-half-ℚˣ) ∙
        ( ap (rational-ℕ 2 *ℚ_) eq-diff-one-one-half-one-half-ℚ) ∙
        ( mul-two-one-half-ℚ)
    in
      ( ap
        ( _*ℚ rational-inv-ℚˣ q-one-half-ℚˣ)
        ( inv eq-mul-two-rational-q-one-half-ℚˣ)) ∙
      ( cancel-right-mul-div-ℚˣ (rational-ℕ 2) q-one-half-ℚˣ)

  leq-zero-sum-standard-geometric-sequence-one-half-ℚ :
    leq-ℚ zero-ℚ sum-standard-geometric-sequence-one-half-ℚ
  leq-zero-sum-standard-geometric-sequence-one-half-ℚ =
    transitive-leq-ℚ
      ( zero-ℚ)
      ( rational-ℕ 2)
      ( sum-standard-geometric-sequence-one-half-ℚ)
      ( leq-eq-ℚ
        ( inv eq-sum-standard-geometric-sequence-one-half-rational-two-ℚ))
      ( preserves-leq-rational-ℕ {0} {2} (leq-zero-ℕ 2))

  leq-one-plus-half-mul-sum-standard-geometric-sequence-one-half-ℚ :
    leq-ℚ
      ( one-ℚ +ℚ
        ( one-half-ℚ *ℚ sum-standard-geometric-sequence-one-half-ℚ))
      ( sum-standard-geometric-sequence-one-half-ℚ)
  leq-one-plus-half-mul-sum-standard-geometric-sequence-one-half-ℚ =
    leq-eq-ℚ
      ( equational-reasoning
        one-ℚ +ℚ (one-half-ℚ *ℚ sum-standard-geometric-sequence-one-half-ℚ)
        ＝ one-ℚ +ℚ (one-half-ℚ *ℚ rational-ℕ 2)
          by
            ap
              ( λ x → one-ℚ +ℚ (one-half-ℚ *ℚ x))
              ( eq-sum-standard-geometric-sequence-one-half-rational-two-ℚ)
        ＝ one-ℚ +ℚ one-ℚ
          by ap (one-ℚ +ℚ_) mul-one-half-two-ℚ
        ＝ rational-ℕ 2
          by twice-one-ℚ
        ＝ sum-standard-geometric-sequence-one-half-ℚ
          by inv eq-sum-standard-geometric-sequence-one-half-rational-two-ℚ)

  leq-two-sum-standard-geometric-one-half-ℚ :
    (k : ℕ) →
    leq-ℚ
      ( sum-standard-geometric-fin-sequence-ℚ one-ℚ one-half-ℚ k)
      ( sum-standard-geometric-sequence-one-half-ℚ)
  leq-two-sum-standard-geometric-one-half-ℚ =
    leq-bound-sum-standard-geometric-fin-sequence-ℚ
      ( one-half-ℚ⁺)
      ( sum-standard-geometric-sequence-one-half-ℚ)
      ( leq-zero-sum-standard-geometric-sequence-one-half-ℚ)
      ( leq-one-plus-half-mul-sum-standard-geometric-sequence-one-half-ℚ)

  leq-rational-two-sum-standard-geometric-one-half-ℚ :
    (k : ℕ) →
    leq-ℚ
      ( sum-standard-geometric-fin-sequence-ℚ one-ℚ one-half-ℚ k)
      ( rational-ℕ 2)
  leq-rational-two-sum-standard-geometric-one-half-ℚ k =
    transitive-leq-ℚ
      ( sum-standard-geometric-fin-sequence-ℚ one-ℚ one-half-ℚ k)
      ( sum-standard-geometric-sequence-one-half-ℚ)
      ( rational-ℕ 2)
      ( leq-eq-ℚ
        ( eq-sum-standard-geometric-sequence-one-half-rational-two-ℚ))
      ( leq-two-sum-standard-geometric-one-half-ℚ k)
```

## External links

- [Geometric progressions](https://en.wikipedia.org/wiki/Geometric_progression)
  at Wikipedia
