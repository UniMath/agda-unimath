# Bernoulli's inequality on the positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.bernoullis-inequality-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.arithmetic-sequences-positive-rational-numbers
open import elementary-number-theory.geometric-sequences-positive-rational-numbers
open import elementary-number-theory.inequality-positive-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.groups
```

</details>

## Idea

{{#concept "Bernoulli's inequality" Disambiguation="on the positive rational numbers" WD="Bernoulli's inequality" WDID=Q728662}}
on the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
states that for any `h : ℚ⁺`, the arithmetic sequence with initial term `1` and
common difference `h` is lesser than or equal to the geometric sequence with
initial term `1` and common ratio `1 + h`:

```text
  ∀ (h : ℚ⁺) (n : ℕ), 1 + n * h ≤ (1 + h)ⁿ
```

## Lemma

The ratio of two consecutive terms of a unitary arithmetic sequence of positive
rational numbers is bounded:

```text
  ∀ (h : ℚ⁺) (n  : ℕ), 1 + (n + 1)h ≤ (1 + n h)(1 + h)
```

```agda
module _
  (h : ℚ⁺)
  where

  abstract
    bounded-ratio-unitary-arithmetic-sequence-ℚ⁺ :
      (n : ℕ) →
      leq-ℚ⁺
        ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h (succ-ℕ n))
        ( mul-ℚ⁺
          ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h n)
          ( one-ℚ⁺ +ℚ⁺ h))
    bounded-ratio-unitary-arithmetic-sequence-ℚ⁺ n =
      inv-tr
        ( leq-ℚ⁺
          ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h (succ-ℕ n)))
        ( ( left-distributive-mul-add-ℚ⁺
            ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h n)
            ( one-ℚ⁺)
            ( h)) ∙
          ( ap
            ( λ x →
              add-ℚ⁺
                ( x)
                ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h n *ℚ⁺ h))
            ( right-unit-law-mul-ℚ⁺
              ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h n))))
        ( preserves-order-right-add-ℚ
          ( rational-ℚ⁺
            ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h n))
          ( rational-ℚ⁺ h)
          ( rational-ℚ⁺
            ( mul-ℚ⁺
              ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h n)
              ( h)))
          ( tr
            ( λ x →
              leq-ℚ
                ( x)
                ( mul-ℚ
                  ( rational-ℚ⁺
                    ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h n))
                  ( rational-ℚ⁺ h)))
            ( left-unit-law-mul-ℚ (rational-ℚ⁺ h))
            ( preserves-order-right-mul-ℚ⁺
              ( h)
              ( one-ℚ)
              ( rational-ℚ⁺
                ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h n))
              ( leq-initial-arithmetic-sequence-ℚ⁺
                ( standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h)
                ( n)))))
```

## Theorem

```text
  ∀ (h : ℚ⁺) (n : ℕ), 1 + n * h ≤ (1 + h)ⁿ
```

```agda
module _
  (h : ℚ⁺)
  where

  abstract
    bernoullis-inequality-ℚ⁺ :
      (n : ℕ) →
      leq-ℚ⁺
        ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h n)
        ( seq-standard-geometric-sequence-ℚ⁺ one-ℚ⁺ (one-ℚ⁺ +ℚ⁺ h) n)
    bernoullis-inequality-ℚ⁺ zero-ℕ = refl-leq-ℚ one-ℚ
    bernoullis-inequality-ℚ⁺ (succ-ℕ n) =
      transitive-leq-ℚ
        ( rational-ℚ⁺
          ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h (succ-ℕ n)))
        ( rational-ℚ⁺
          ( mul-ℚ⁺
            ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h n)
            ( one-ℚ⁺ +ℚ⁺ h)))
        ( rational-ℚ⁺
          ( seq-standard-geometric-sequence-ℚ⁺
            ( one-ℚ⁺)
            ( one-ℚ⁺ +ℚ⁺ h)
            ( succ-ℕ n)))
        ( preserves-order-right-mul-ℚ⁺
          ( one-ℚ⁺ +ℚ⁺ h)
          ( rational-ℚ⁺
            (seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h n))
          ( rational-ℚ⁺
            ( seq-standard-geometric-sequence-ℚ⁺ one-ℚ⁺ (one-ℚ⁺ +ℚ⁺ h) n))
          ( bernoullis-inequality-ℚ⁺ n))
        ( bounded-ratio-unitary-arithmetic-sequence-ℚ⁺ h n)
```

## External links

- [Bernoulli's inequality](https://en.wikipedia.org/wiki/Bernoulli%27s_inequality)
  at Wikipedia
