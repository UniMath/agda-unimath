# Geometric sequences of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.geometric-sequences-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.geometric-sequences-commutative-rings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings

open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.powers-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.identity-types
open import foundation.negated-equality
open import foundation.universe-levels

open import group-theory.groups

open import lists.sequences

open import order-theory.strictly-increasing-sequences-strictly-preordered-sets
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
      ( a *ℚ
        ( (one-ℚ -ℚ power-ℚ n r) *ℚ
          rational-inv-ℚˣ (invertible-diff-neq-ℚ r one-ℚ r≠1)))
    compute-sum-standard-geometric-fin-sequence-ℚ 0 =
      inv
        ( equational-reasoning
          a *ℚ ((one-ℚ -ℚ one-ℚ) *ℚ _)
          ＝ a *ℚ (zero-ℚ *ℚ _)
            by
              ap-mul-ℚ
                ( refl)
                ( ap-mul-ℚ (right-inverse-law-add-ℚ one-ℚ) refl)
          ＝ a *ℚ zero-ℚ
            by ap-mul-ℚ refl (left-zero-law-mul-ℚ _)
          ＝ zero-ℚ
            by right-zero-law-mul-ℚ a)
    compute-sum-standard-geometric-fin-sequence-ℚ (succ-ℕ n) =
      let
        1/⟨1-r⟩ = rational-inv-ℚˣ (invertible-diff-neq-ℚ r one-ℚ r≠1)
      in
        equational-reasoning
          sum-standard-geometric-fin-sequence-ℚ a r (succ-ℕ n)
          ＝
            sum-standard-geometric-fin-sequence-ℚ a r n +ℚ
            seq-standard-geometric-sequence-ℚ a r n
            by
              cons-sum-fin-sequence-type-Commutative-Ring
                ( commutative-ring-ℚ)
                ( n)
                ( _)
                ( refl)
          ＝
            ( a *ℚ
              ( (one-ℚ -ℚ power-ℚ n r) *ℚ 1/1-r)) +ℚ
            ( a *ℚ power-ℚ n r)
            by
              ap-add-ℚ
                ( compute-sum-standard-geometric-fin-sequence-ℚ n)
                ( compute-standard-geometric-sequence-ℚ a r n)
          ＝
            a *ℚ
            (((one-ℚ -ℚ power-ℚ n r) *ℚ 1/1-r) +ℚ power-ℚ n r)
            by inv (left-distributive-mul-add-ℚ a _ _)
          ＝
            a *ℚ
            ( (((one-ℚ -ℚ power-ℚ n r) *ℚ 1/1-r) +ℚ
              (power-ℚ n r *ℚ (one-ℚ -ℚ r)) *ℚ 1/1-r))
            by
              ap-mul-ℚ
                ( refl)
                ( ap-add-ℚ
                  ( refl)
                  ( inv
                    ( cancel-right-mul-div-ℚˣ _
                      ( invertible-diff-neq-ℚ r one-ℚ r≠1))))
          ＝
            a *ℚ
            ( ( (one-ℚ -ℚ power-ℚ n r) +ℚ (power-ℚ n r *ℚ (one-ℚ -ℚ r))) *ℚ
              1/1-r)
            by
              ap-mul-ℚ
                ( refl)
                ( inv (right-distributive-mul-add-ℚ _ _ 1/1-r))
          ＝
            a *ℚ
            ( ( one-ℚ -ℚ power-ℚ n r +ℚ
                ((power-ℚ n r *ℚ one-ℚ) -ℚ (power-ℚ n r *ℚ r))) *ℚ
              1/1-r)
            by
              ap-mul-ℚ
                ( refl)
                ( ap-mul-ℚ
                  ( ap-add-ℚ refl (left-distributive-mul-diff-ℚ _ _ _))
                  ( refl))
          ＝
            a *ℚ
            ( ( one-ℚ -ℚ power-ℚ n r +ℚ
                ((power-ℚ n r -ℚ power-ℚ (succ-ℕ n) r))) *ℚ
              1/1-r)
            by
              ap-mul-ℚ
                ( refl)
                ( ap-mul-ℚ
                  ( ap-add-ℚ
                    ( refl)
                    ( ap-diff-ℚ
                      ( right-unit-law-mul-ℚ _)
                      ( inv (power-succ-ℚ n r))))
                  ( refl))
          ＝ a *ℚ ((one-ℚ -ℚ power-ℚ (succ-ℕ n) r) *ℚ 1/1-r)
            by
              ap-mul-ℚ
                ( refl)
                ( ap-mul-ℚ
                  ( mul-right-div-Group group-add-ℚ _ _ _)
                  ( refl))
```

## External links

- [Geometric progressions](https://en.wikipedia.org/wiki/Geometric_progression)
  at Wikipedia
