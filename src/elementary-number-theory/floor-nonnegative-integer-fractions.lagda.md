# The floor of nonnegative integer fractions

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.floor-nonnegative-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.inequality-integer-fractions
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integer-fractions
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.strict-inequality-integer-fractions
open import elementary-number-theory.strict-inequality-integers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications

open import order-theory.posets
```

</details>

## Idea

The
{{#concept "floor" Disambiguation="of a nonnegative rational number" Agda=floor-is-nonnegative-fraction-ℤ}}
of a [nonnegative](elementary-number-theory.nonnegative-integer-fractions.md)
[integer fraction](elementary-number-theory.integer-fractions.md) `q` is the
[greatest](elementary-number-theory.inequality-integers.md)
[integer](elementary-number-theory.integers.md) `x` such that `in-fraction-ℤ x`
is
[less than or equal to](elementary-number-theory.inequality-integer-fractions.md)
`q`.

The constraint that `q` is nonnegative guarantees that `x` is
[nonnegative](elementary-number-theory.nonnegative-integers.md).

## Definition

```agda
module _
  (x : fraction-ℤ)
  (0≤x : is-nonnegative-fraction-ℤ x)
  where

  opaque
    nat-floor-is-nonnegative-fraction-ℤ : ℕ
    nat-floor-is-nonnegative-fraction-ℤ =
      let
        (p , q⁺) = x
      in quotient-euclidean-division-ℕ (nat-ℤ⁺ q⁺) (nat-nonnegative-ℤ (p , 0≤x))

  floor-is-nonnegative-fraction-ℤ : ℤ
  floor-is-nonnegative-fraction-ℤ = int-ℕ nat-floor-is-nonnegative-fraction-ℤ
```

## Properties

### The floor of a nonnegative integer fraction is less than or equal to the fraction

```agda
module _
  (x : fraction-ℤ)
  (0≤x : is-nonnegative-fraction-ℤ x)
  where

  abstract opaque
    unfolding nat-floor-is-nonnegative-fraction-ℤ

    leq-floor-is-nonnegative-fraction-ℤ :
      leq-fraction-ℤ (in-fraction-ℤ (floor-is-nonnegative-fraction-ℤ x 0≤x)) x
    leq-floor-is-nonnegative-fraction-ℤ =
      let
        (p , q⁺@(q , _)) = x
        pℕ = nat-nonnegative-ℤ (p , 0≤x)
        (qℕ , qℕ≠0) = positive-nat-ℤ⁺ q⁺
        n = quotient-euclidean-division-ℕ qℕ pℕ
        k = remainder-euclidean-division-ℕ qℕ pℕ
        open inequality-reasoning-Poset ℤ-Poset
      in
        chain-of-inequalities
        int-ℕ n *ℤ q
        ≤ int-ℕ n *ℤ int-ℕ qℕ
          by
            leq-eq-ℤ
              ( ap-mul-ℤ refl (ap int-ℤ⁺ (inv (is-section-positive-nat-ℤ⁺ q⁺))))
        ≤ int-ℕ (n *ℕ qℕ)
          by leq-eq-ℤ (mul-int-ℕ _ _)
        ≤ int-ℕ (n *ℕ qℕ +ℕ k)
          by leq-int-ℕ (n *ℕ qℕ) (n *ℕ qℕ +ℕ k) (leq-add-ℕ (n *ℕ qℕ) k)
        ≤ int-ℕ pℕ
          by leq-eq-ℤ (ap int-ℕ (eq-euclidean-division-ℕ qℕ pℕ))
        ≤ p
          by
            leq-eq-ℤ
              ( ap int-nonnegative-ℤ (is-section-nat-nonnegative-ℤ (p , 0≤x)))
        ≤ p *ℤ one-ℤ
          by leq-eq-ℤ (inv (right-unit-law-mul-ℤ p))
```

### A nonnegative integer fraction is less than or equal to the successor of its floor

```agda
module _
  (x : fraction-ℤ)
  (0≤x : is-nonnegative-fraction-ℤ x)
  where

  abstract opaque
    unfolding nat-floor-is-nonnegative-fraction-ℤ

    le-succ-nat-floor-is-nonnegative-fraction-ℤ :
      le-fraction-ℤ
        ( x)
        ( int-fraction-ℕ (succ-ℕ (nat-floor-is-nonnegative-fraction-ℤ x 0≤x)))
    le-succ-nat-floor-is-nonnegative-fraction-ℤ =
      let
        (p , q⁺@(q , _)) = x
        pℕ = nat-nonnegative-ℤ (p , 0≤x)
        (qℕ , qℕ≠0) = positive-nat-ℤ⁺ q⁺
        n = quotient-euclidean-division-ℕ qℕ pℕ
        k = remainder-euclidean-division-ℕ qℕ pℕ
        nq+k=p1 =
          ( ap int-ℕ (eq-euclidean-division-ℕ qℕ pℕ)) ∙
          ( ap int-nonnegative-ℤ (is-section-nat-nonnegative-ℤ (p , 0≤x))) ∙
          ( inv (right-unit-law-mul-ℤ p))
      in
        binary-tr
          ( le-ℤ)
          ( equational-reasoning
            int-ℕ (n *ℕ qℕ) +ℤ int-ℕ k
            ＝ int-ℕ (n *ℕ qℕ +ℕ k)
              by add-int-ℕ _ _
            ＝ int-ℕ pℕ
              by ap int-ℕ (eq-euclidean-division-ℕ qℕ pℕ)
            ＝ p
              by ap int-nonnegative-ℤ (is-section-nat-nonnegative-ℤ (p , 0≤x))
            ＝ p *ℤ one-ℤ
              by inv (right-unit-law-mul-ℤ p))
          ( equational-reasoning
            int-ℕ (n *ℕ qℕ) +ℤ int-ℕ qℕ
            ＝ (int-ℕ n *ℤ int-ℕ qℕ) +ℤ int-ℕ qℕ
              by ap-add-ℤ (inv (mul-int-ℕ n qℕ)) refl
            ＝ succ-ℤ (int-ℕ n) *ℤ int-ℕ qℕ
              by inv (left-successor-law-mul-ℤ' (int-ℕ n) (int-ℕ qℕ))
            ＝ int-ℕ (succ-ℕ n) *ℤ q
              by
                ap-mul-ℤ
                  ( succ-int-ℕ n)
                  ( ap int-ℤ⁺ (is-section-positive-nat-ℤ⁺ q⁺)))
          ( preserves-le-right-add-ℤ
            ( int-ℕ (n *ℕ qℕ))
            ( int-ℕ k)
            ( int-ℕ qℕ)
            ( preserves-le-int-ℕ _ _
              ( strict-upper-bound-remainder-euclidean-division-ℕ
                ( qℕ)
                ( pℕ)
                ( qℕ≠0))))

    le-succ-floor-is-nonnegative-fraction-ℤ :
      le-fraction-ℤ
        ( x)
        ( in-fraction-ℤ (succ-ℤ (floor-is-nonnegative-fraction-ℤ x 0≤x)))
    le-succ-floor-is-nonnegative-fraction-ℤ =
      inv-tr
        ( λ k → le-fraction-ℤ x (in-fraction-ℤ k))
        ( succ-int-ℕ (nat-floor-is-nonnegative-fraction-ℤ x 0≤x))
        ( le-succ-nat-floor-is-nonnegative-fraction-ℤ)
```
