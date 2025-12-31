# Geometric sequences of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.geometric-sequences-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.convergent-series-real-numbers
open import analysis.series-real-numbers

open import commutative-algebra.geometric-sequences-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.apartness-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.isometry-difference-real-numbers
open import real-numbers.large-ring-of-real-numbers
open import real-numbers.limits-sequences-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-nonzero-real-numbers
open import real-numbers.nonzero-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.uniformly-continuous-endofunctions-real-numbers
```

</details>

## Idea

A
{{#concept "geometric sequence" Disambiguation="of real numbers" Agda=geometric-sequence-ℝ}}
of [real numbers](real-numbers.dedekind-real-numbers.md) is a
[geometric sequence](commutative-algebra.geometric-sequences-commutative-rings.md)
in the
[commutative ring of real numbers](real-numbers.large-ring-of-real-numbers.md).

## Definitions

```agda
geometric-sequence-ℝ : (l : Level) → UU (lsuc l)
geometric-sequence-ℝ l =
  geometric-sequence-Commutative-Ring (commutative-ring-ℝ l)

seq-geometric-sequence-ℝ : {l : Level} → geometric-sequence-ℝ l → sequence (ℝ l)
seq-geometric-sequence-ℝ {l} =
  seq-geometric-sequence-Commutative-Ring (commutative-ring-ℝ l)

standard-geometric-sequence-ℝ :
  {l : Level} → ℝ l → ℝ l → geometric-sequence-ℝ l
standard-geometric-sequence-ℝ {l} =
  standard-geometric-sequence-Commutative-Ring (commutative-ring-ℝ l)

seq-standard-geometric-sequence-ℝ :
  {l : Level} → ℝ l → ℝ l → sequence (ℝ l)
seq-standard-geometric-sequence-ℝ {l} =
  seq-standard-geometric-sequence-Commutative-Ring (commutative-ring-ℝ l)
```

## Properties

### The nth term of a geometric sequence with initial term `a` and common ratio `r` is `a * rⁿ`

```agda
module _
  {l : Level} (a r : ℝ l)
  where

  compute-standard-geometric-sequence-ℝ :
    (n : ℕ) → seq-standard-geometric-sequence-ℝ a r n ＝ a *ℝ power-ℝ n r
  compute-standard-geometric-sequence-ℝ n =
    inv
      ( htpy-mul-pow-standard-geometric-sequence-Commutative-Ring
        ( commutative-ring-ℝ l)
        ( a)
        ( r)
        ( n))
```

### If `r` is apart from `1`, the sum of the first `n` elements of the standard geometric sequence `n ↦ arⁿ` is `a(1-rⁿ)/(1-r)`

```agda
sum-standard-geometric-fin-sequence-ℝ : {l : Level} → ℝ l → ℝ l → ℕ → ℝ l
sum-standard-geometric-fin-sequence-ℝ {l} =
  sum-standard-geometric-fin-sequence-Commutative-Ring (commutative-ring-ℝ l)

module _
  {l : Level} (a r : ℝ l) (r≠1 : apart-ℝ r one-ℝ)
  where

  abstract
    compute-sum-standard-geometric-fin-sequence-ℝ :
      (n : ℕ) →
      sum-standard-geometric-fin-sequence-ℝ a r n ＝
      ( ( a *ℝ
          real-inv-nonzero-ℝ
            ( nonzero-diff-apart-ℝ one-ℝ r (symmetric-apart-ℝ r≠1))) *ℝ
        (one-ℝ -ℝ power-ℝ n r))
    compute-sum-standard-geometric-fin-sequence-ℝ n =
      let
        1#r = symmetric-apart-ℝ r≠1
        1l#r =
          apart-left-sim-ℝ
            ( r)
            ( one-ℝ)
            ( raise-ℝ l one-ℝ)
            ( sim-raise-ℝ l one-ℝ)
            ( 1#r)
      in
        equational-reasoning
          sum-standard-geometric-fin-sequence-ℝ a r n
          ＝
            ( a *ℝ
              real-inv-nonzero-ℝ
                ( nonzero-diff-apart-ℝ (raise-ℝ l one-ℝ) r 1l#r)) *ℝ
            ( raise-ℝ l one-ℝ -ℝ power-ℝ n r)
            by
              compute-sum-standard-geometric-fin-sequence-Commutative-Ring
                ( commutative-ring-ℝ l)
                ( a)
                ( r)
                ( is-invertible-is-nonzero-ℝ _
                  ( is-nonzero-diff-is-apart-ℝ _ _ 1l#r))
                ( n)
          ＝
            ( a *ℝ real-inv-nonzero-ℝ (nonzero-diff-apart-ℝ one-ℝ r 1#r)) *ℝ
            ( one-ℝ -ℝ power-ℝ n r)
            by
              ap-mul-ℝ
                ( ap-mul-ℝ
                  ( refl)
                  ( ap
                    ( real-inv-nonzero-ℝ)
                    ( eq-nonzero-ℝ _ _
                      ( eq-sim-ℝ
                        ( preserves-sim-diff-ℝ
                          ( symmetric-sim-ℝ (sim-raise-ℝ l one-ℝ))
                          ( refl-sim-ℝ r))))))
                ( eq-sim-ℝ
                  ( preserves-sim-diff-ℝ
                    ( symmetric-sim-ℝ (sim-raise-ℝ l one-ℝ))
                    ( refl-sim-ℝ (power-ℝ n r))))
```

### If `|r| < 1`, then the geometric series `Σₙ arⁿ` converges to `a/(1-r)`

This is the [66th](literature.100-theorems.md#66) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

```agda
module _
  {l : Level} (a r : ℝ l)
  where

  standard-geometric-series-ℝ : series-ℝ l
  standard-geometric-series-ℝ =
    series-terms-ℝ (seq-standard-geometric-sequence-ℝ a r)

  abstract
    compute-sum-standard-geometric-series-ℝ :
      (|r|<1 : le-ℝ (abs-ℝ r) one-ℝ) →
      is-sum-series-ℝ
        ( standard-geometric-series-ℝ)
        ( a *ℝ real-inv-nonzero-ℝ (nonzero-diff-le-abs-ℝ |r|<1))
    compute-sum-standard-geometric-series-ℝ |r|<1 =
      let
        r#1 = apart-le-ℝ (concatenate-leq-le-ℝ _ _ _ (leq-abs-ℝ r) |r|<1)
      in
        binary-tr
          ( is-limit-sequence-ℝ)
          ( inv
            ( eq-htpy
              ( λ n →
                equational-reasoning
                  sum-standard-geometric-fin-sequence-ℝ a r n
                  ＝
                    ( a *ℝ real-inv-nonzero-ℝ _) *ℝ
                    ( one-ℝ -ℝ power-ℝ n r)
                    by compute-sum-standard-geometric-fin-sequence-ℝ a r r#1 n
                  ＝
                    ( a *ℝ real-inv-nonzero-ℝ (nonzero-diff-le-abs-ℝ |r|<1)) *ℝ
                    ( one-ℝ -ℝ power-ℝ n r)
                    by
                      ap
                        ( λ z →
                          (a *ℝ real-inv-nonzero-ℝ z) *ℝ (one-ℝ -ℝ power-ℝ n r))
                        ( eq-nonzero-ℝ
                          ( nonzero-diff-apart-ℝ
                            ( one-ℝ)
                            ( r)
                            ( symmetric-apart-ℝ r#1))
                          ( nonzero-diff-le-abs-ℝ |r|<1)
                          ( refl)))))
          ( equational-reasoning
            ( a *ℝ real-inv-nonzero-ℝ (nonzero-diff-le-abs-ℝ |r|<1)) *ℝ
            ( one-ℝ -ℝ raise-zero-ℝ l)
            ＝
              ( a *ℝ real-inv-nonzero-ℝ (nonzero-diff-le-abs-ℝ |r|<1)) *ℝ
              ( one-ℝ -ℝ zero-ℝ)
              by
                eq-sim-ℝ
                  ( preserves-sim-left-mul-ℝ _ _ _
                    ( preserves-sim-diff-ℝ
                      ( refl-sim-ℝ one-ℝ)
                      ( symmetric-sim-ℝ (sim-raise-ℝ l zero-ℝ))))
            ＝
              ( a *ℝ real-inv-nonzero-ℝ (nonzero-diff-le-abs-ℝ |r|<1)) *ℝ one-ℝ
              by ap-mul-ℝ refl (right-unit-law-diff-ℝ one-ℝ)
            ＝ a *ℝ real-inv-nonzero-ℝ (nonzero-diff-le-abs-ℝ |r|<1)
              by right-unit-law-mul-ℝ _)
          ( preserves-limits-sequence-uniformly-continuous-endo-ℝ
            ( comp-uniformly-continuous-endo-ℝ
              ( uniformly-continuous-right-mul-ℝ
                ( l)
                ( a *ℝ real-inv-nonzero-ℝ (nonzero-diff-le-abs-ℝ |r|<1)))
              ( uniformly-continuous-diff-ℝ one-ℝ))
            ( λ n → power-ℝ n r)
            ( raise-zero-ℝ l)
            ( is-zero-lim-power-le-one-abs-ℝ r |r|<1))

  convergent-standard-geometric-series-ℝ :
    le-ℝ (abs-ℝ r) one-ℝ → convergent-series-ℝ l
  convergent-standard-geometric-series-ℝ |r|<1 =
    ( standard-geometric-series-ℝ ,
      a *ℝ real-inv-nonzero-ℝ (nonzero-diff-le-abs-ℝ |r|<1) ,
      compute-sum-standard-geometric-series-ℝ |r|<1)
```

## References

{{#bibliography}}
