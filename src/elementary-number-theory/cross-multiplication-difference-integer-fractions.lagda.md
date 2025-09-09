# The cross-multiplication difference of two integer fractions

```agda
module elementary-number-theory.cross-multiplication-difference-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
```

</details>

## Idea

The
{{#concept "cross-multiplication difference" Agda=cross-mul-diff-fraction-ℤ}} of
two [integer fractions](elementary-number-theory.integer-fractions.md) `a/b` and
`c/d` is the [difference](elementary-number-theory.difference-integers.md) of
the [products](elementary-number-theory.multiplication-integers.md) of the
numerator of each fraction with the denominator of the other: `c * b - a * d`.

## Definitions

### The cross-multiplication difference of two fractions

```agda
cross-mul-diff-fraction-ℤ : fraction-ℤ → fraction-ℤ → ℤ
cross-mul-diff-fraction-ℤ x y =
  diff-ℤ
    ( numerator-fraction-ℤ y *ℤ denominator-fraction-ℤ x)
    ( numerator-fraction-ℤ x *ℤ denominator-fraction-ℤ y)
```

## Properties

### Swapping the fractions changes the sign of the cross-multiplication difference

```agda
abstract
  skew-commutative-cross-mul-diff-fraction-ℤ :
    (x y : fraction-ℤ) →
    neg-ℤ (cross-mul-diff-fraction-ℤ x y) ＝ cross-mul-diff-fraction-ℤ y x
  skew-commutative-cross-mul-diff-fraction-ℤ x y =
    distributive-neg-diff-ℤ
      ( numerator-fraction-ℤ y *ℤ denominator-fraction-ℤ x)
      ( numerator-fraction-ℤ x *ℤ denominator-fraction-ℤ y)
```

### The cross multiplication difference of zero and an integer fraction is its numerator

```agda
module _
  (x : fraction-ℤ)
  where

  abstract
    cross-mul-diff-zero-fraction-ℤ :
      cross-mul-diff-fraction-ℤ zero-fraction-ℤ x ＝ numerator-fraction-ℤ x
    cross-mul-diff-zero-fraction-ℤ =
      ( right-unit-law-add-ℤ (numerator-fraction-ℤ x *ℤ one-ℤ)) ∙
      ( right-unit-law-mul-ℤ (numerator-fraction-ℤ x))
```

### The cross multiplication difference of one and an integer fraction is the difference of its numerator and denominator

```agda
module _
  (x : fraction-ℤ)
  where

  abstract
    cross-mul-diff-one-fraction-ℤ :
      cross-mul-diff-fraction-ℤ one-fraction-ℤ x ＝
      (numerator-fraction-ℤ x) -ℤ (denominator-fraction-ℤ x)
    cross-mul-diff-one-fraction-ℤ =
      ap-diff-ℤ
        ( right-unit-law-mul-ℤ (numerator-fraction-ℤ x))
        ( left-unit-law-mul-ℤ (denominator-fraction-ℤ x))
```

### Two fractions are similar when their cross-multiplication difference is zero

```agda
module _
  (x y : fraction-ℤ)
  where

  abstract
    is-zero-cross-mul-diff-sim-fraction-ℤ :
      sim-fraction-ℤ x y →
      is-zero-ℤ (cross-mul-diff-fraction-ℤ x y)
    is-zero-cross-mul-diff-sim-fraction-ℤ H =
      is-zero-diff-ℤ (inv H)

    sim-is-zero-coss-mul-diff-fraction-ℤ :
      is-zero-ℤ (cross-mul-diff-fraction-ℤ x y) →
      sim-fraction-ℤ x y
    sim-is-zero-coss-mul-diff-fraction-ℤ H = inv (eq-diff-ℤ H)
```

## The transitive-additive property for the cross-multiplication difference

Given three fractions `a/b`, `x/y` and `m/n`, the pairwise cross-multiplication
differences satisfy a transitive-additive property:

```text
  y * (m * b - a * n) = b * (m * y - x * n) + n * (x * b - a * y)
```

```agda
abstract
  lemma-add-cross-mul-diff-fraction-ℤ :
    (p q r : fraction-ℤ) →
    ( add-ℤ
      ( denominator-fraction-ℤ p *ℤ cross-mul-diff-fraction-ℤ q r)
      ( denominator-fraction-ℤ r *ℤ cross-mul-diff-fraction-ℤ p q)) ＝
    ( denominator-fraction-ℤ q *ℤ cross-mul-diff-fraction-ℤ p r)
  lemma-add-cross-mul-diff-fraction-ℤ
    (np , dp , hp)
    (nq , dq , hq)
    (nr , dr , hr) =
    equational-reasoning
    add-ℤ
      (dp *ℤ (nr *ℤ dq -ℤ nq *ℤ dr))
      (dr *ℤ (nq *ℤ dp -ℤ np *ℤ dq))
    ＝ add-ℤ
        (dp *ℤ (nr *ℤ dq) -ℤ dp *ℤ (nq *ℤ dr))
        (dr *ℤ (nq *ℤ dp) -ℤ dr *ℤ (np *ℤ dq))
      by
        ap-add-ℤ
          ( left-distributive-mul-diff-ℤ dp (nr *ℤ dq) (nq *ℤ dr))
          ( left-distributive-mul-diff-ℤ dr (nq *ℤ dp) (np *ℤ dq))
    ＝ diff-ℤ
        (dp *ℤ (nr *ℤ dq) +ℤ dr *ℤ (nq *ℤ dp))
        (dp *ℤ (nq *ℤ dr) +ℤ dr *ℤ (np *ℤ dq))
      by
        interchange-law-add-diff-ℤ
          ( mul-ℤ dp ( mul-ℤ nr dq))
          ( mul-ℤ dp ( mul-ℤ nq dr))
          ( mul-ℤ dr ( mul-ℤ nq dp))
          ( mul-ℤ dr ( mul-ℤ np dq))
    ＝ diff-ℤ
        (dq *ℤ (nr *ℤ dp) +ℤ dr *ℤ (nq *ℤ dp))
        (dr *ℤ (nq *ℤ dp) +ℤ dq *ℤ (np *ℤ dr))
      by
        ap-diff-ℤ
          ( ap-add-ℤ
            ( lemma-interchange-mul-ℤ dp nr dq)
            ( refl))
          ( ap-add-ℤ
            ( lemma-interchange-mul-ℤ dp nq dr)
            ( lemma-interchange-mul-ℤ dr np dq))
    ＝ diff-ℤ
        (dq *ℤ (nr *ℤ dp) +ℤ dr *ℤ (nq *ℤ dp))
        ((dq *ℤ (np *ℤ dr)) +ℤ (dr *ℤ (nq *ℤ dp)))
      by
        ap
          ( diff-ℤ (dq *ℤ (nr *ℤ dp) +ℤ dr *ℤ (nq *ℤ dp)))
          ( commutative-add-ℤ (dr *ℤ (nq *ℤ dp)) (dq *ℤ (np *ℤ dr)))
    ＝ (dq *ℤ (nr *ℤ dp)) -ℤ (dq *ℤ (np *ℤ dr))
      by
        right-translation-diff-ℤ
          (dq *ℤ (nr *ℤ dp))
          (dq *ℤ (np *ℤ dr))
          (dr *ℤ (nq *ℤ dp))
    ＝ dq *ℤ (nr *ℤ dp -ℤ np *ℤ dr)
      by inv (left-distributive-mul-diff-ℤ dq (nr *ℤ dp) (np *ℤ dr))
    where
    lemma-interchange-mul-ℤ : (a b c : ℤ) → (a *ℤ (b *ℤ c)) ＝ (c *ℤ (b *ℤ a))
    lemma-interchange-mul-ℤ a b c =
      inv (associative-mul-ℤ a b c) ∙
      ap (mul-ℤ' c) (commutative-mul-ℤ a b) ∙
      commutative-mul-ℤ (b *ℤ a) c

  lemma-left-sim-cross-mul-diff-fraction-ℤ :
    (a a' b : fraction-ℤ) →
    sim-fraction-ℤ a a' →
    denominator-fraction-ℤ a *ℤ cross-mul-diff-fraction-ℤ a' b ＝
    denominator-fraction-ℤ a' *ℤ cross-mul-diff-fraction-ℤ a b
  lemma-left-sim-cross-mul-diff-fraction-ℤ a a' b H =
    equational-reasoning
    ( denominator-fraction-ℤ a *ℤ cross-mul-diff-fraction-ℤ a' b)
    ＝ ( add-ℤ
          ( denominator-fraction-ℤ a' *ℤ cross-mul-diff-fraction-ℤ a b)
          ( denominator-fraction-ℤ b *ℤ cross-mul-diff-fraction-ℤ a' a))
      by inv (lemma-add-cross-mul-diff-fraction-ℤ a' a b)
    ＝ ( add-ℤ
        ( denominator-fraction-ℤ a' *ℤ cross-mul-diff-fraction-ℤ a b)
        ( zero-ℤ))
      by
        ap
          ( add-ℤ
            ( denominator-fraction-ℤ a' *ℤ cross-mul-diff-fraction-ℤ a b))
            ( ( ap
                ( mul-ℤ (denominator-fraction-ℤ b))
                ( is-zero-cross-mul-diff-sim-fraction-ℤ a' a H')) ∙
              ( right-zero-law-mul-ℤ (denominator-fraction-ℤ b)))
    ＝ denominator-fraction-ℤ a' *ℤ cross-mul-diff-fraction-ℤ a b
      by
        right-unit-law-add-ℤ
          ( denominator-fraction-ℤ a' *ℤ cross-mul-diff-fraction-ℤ a b)
    where
    H' : sim-fraction-ℤ a' a
    H' = symmetric-sim-fraction-ℤ a a' H

  lemma-right-sim-cross-mul-diff-fraction-ℤ :
    (a b b' : fraction-ℤ) →
    sim-fraction-ℤ b b' →
    denominator-fraction-ℤ b *ℤ cross-mul-diff-fraction-ℤ a b' ＝
    denominator-fraction-ℤ b' *ℤ cross-mul-diff-fraction-ℤ a b
  lemma-right-sim-cross-mul-diff-fraction-ℤ a b b' H =
    equational-reasoning
    ( denominator-fraction-ℤ b *ℤ cross-mul-diff-fraction-ℤ a b')
    ＝ ( add-ℤ
        ( denominator-fraction-ℤ a *ℤ cross-mul-diff-fraction-ℤ b b')
        ( denominator-fraction-ℤ b' *ℤ cross-mul-diff-fraction-ℤ a b))
      by inv (lemma-add-cross-mul-diff-fraction-ℤ a b b')
    ＝ ( add-ℤ
        ( zero-ℤ)
        ( denominator-fraction-ℤ b' *ℤ cross-mul-diff-fraction-ℤ a b))
      by
        ap
          ( add-ℤ' (denominator-fraction-ℤ b' *ℤ cross-mul-diff-fraction-ℤ a b))
          ( ( ap
            ( mul-ℤ (denominator-fraction-ℤ a))
            ( is-zero-cross-mul-diff-sim-fraction-ℤ b b' H)) ∙
            ( right-zero-law-mul-ℤ (denominator-fraction-ℤ a)))
    ＝ denominator-fraction-ℤ b' *ℤ cross-mul-diff-fraction-ℤ a b
      by
        left-unit-law-add-ℤ
          ( denominator-fraction-ℤ b' *ℤ cross-mul-diff-fraction-ℤ a b)
```

## External links

- [Cross-multiplication](https://en.wikipedia.org/wiki/Cross-multiplication) at
  Wikipedia
