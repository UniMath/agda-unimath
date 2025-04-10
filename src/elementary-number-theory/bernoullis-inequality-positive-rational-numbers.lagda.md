# Bernouilli's inequality on the positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.bernoullis-inequality-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.arithmetic-sequences-positive-rational-numbers
open import elementary-number-theory.geometric-sequences-positive-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.zero-approximations-sequences-positive-rational-numbers

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

open import order-theory.infinite-limit-sequences-preorders
```

</details>

## Idea

{{#concept "Bernoulli's inequality" Disambiguation="on the positive rational numbers" WD="Bernoulli's inequality" WDID=Q728662}}
on the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md);
for any `h : ℚ⁺`, the arithmetic sequence with initial term `1` and common
difference `h` is lesser than or equal to the geometric sequence with initial
term `1` and common ratio `1 + h`:

```text
∀ (h : ℚ⁺) (n : ℕ) → 1 + n h ≤ (1 + h)ⁿ
```

It follows that the geometric sequences `(1 + h)ⁿ`
[tend to infinity](order-theory.infinite-limit-sequences-preorders.md) in ℚ⁺.

## Lemma

The ratio of two consecutive terms of a unitary arithmetic sequence of positive
rational numbers is bounded:

```text
∀ (h : ℚ⁺) (n  : ℕ) → 1 + (n + 1)h ≤ (1 + n h)(1 + h)
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
        ( preserves-leq-right-add-ℚ
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
            ( preserves-leq-right-mul-ℚ⁺
              ( h)
              ( one-ℚ)
              ( rational-ℚ⁺
                ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h n))
              ( leq-init-arithmetic-sequence-ℚ⁺
                ( standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h)
                ( n)))))
```

## Bernouilli's inequality on the positive rational numbers

```text
∀ (h : ℚ⁺) (n : ℕ) → 1 + n h ≤ (1 + h)ⁿ
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
        ( preserves-leq-right-mul-ℚ⁺
          ( one-ℚ⁺ +ℚ⁺ h)
          ( rational-ℚ⁺
            (seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h n))
          ( rational-ℚ⁺
            ( seq-standard-geometric-sequence-ℚ⁺ one-ℚ⁺ (one-ℚ⁺ +ℚ⁺ h) n))
          ( bernoullis-inequality-ℚ⁺ n))
        ( bounded-ratio-unitary-arithmetic-sequence-ℚ⁺ h n)
```

## Applications

### The standard geometric sequence with inital term `1` and common ratio `1 + h` tends to infinity

```agda
module _
  (h : ℚ⁺)
  where

  modulus-limit-∞-standard-unitary-onep-geometric-sequence-ℚ⁺ :
    modulus-limit-∞-sequence-Preorder
      ( preorder-ℚ⁺)
      ( seq-standard-geometric-sequence-ℚ⁺ one-ℚ⁺ (one-ℚ⁺ +ℚ⁺ h))
  modulus-limit-∞-standard-unitary-onep-geometric-sequence-ℚ⁺ =
    modulus-leq-modulus-limit-∞-sequence-Preorder
      ( preorder-ℚ⁺)
      ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h)
      ( seq-standard-geometric-sequence-ℚ⁺ one-ℚ⁺ (one-ℚ⁺ +ℚ⁺ h))
      ( bernoullis-inequality-ℚ⁺ h)
      ( modulus-limit-∞-arithmetic-sequence-ℚ⁺
        ( standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h))

  is-limit-∞-standard-unitary-onep-geometric-sequence-ℚ⁺ :
    is-limit-∞-sequence-Preorder
      ( preorder-ℚ⁺)
      ( seq-standard-geometric-sequence-ℚ⁺ one-ℚ⁺ (one-ℚ⁺ +ℚ⁺ h))
  is-limit-∞-standard-unitary-onep-geometric-sequence-ℚ⁺ =
    is-upward-closed-limit-∞-sequence-Preorder
      ( preorder-ℚ⁺)
      ( seq-standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h)
      ( seq-standard-geometric-sequence-ℚ⁺ one-ℚ⁺ (one-ℚ⁺ +ℚ⁺ h))
      ( bernoullis-inequality-ℚ⁺ h)
      ( is-limit-∞-arithmetic-sequence-ℚ⁺
        ( standard-arithmetic-sequence-ℚ⁺ one-ℚ⁺ h))
```

### A geometric sequence of positive rational numbers with initial term `1` and common ratio `r > 1` tends to infinity

```agda
module _
  ( u : geometric-sequence-ℚ⁺)
  ( is-one-init : one-ℚ⁺ ＝ init-term-geometric-sequence-ℚ⁺ u)
  ( 1<r : le-ℚ⁺ one-ℚ⁺ (common-ratio-geometric-sequence-ℚ⁺ u))
  where

  modulus-limit-∞-seq-unitary-geometric-sequence-ℚ⁺ :
    modulus-limit-∞-sequence-Preorder
      ( preorder-ℚ⁺)
      ( seq-geometric-sequence-ℚ⁺ u)
  modulus-limit-∞-seq-unitary-geometric-sequence-ℚ⁺ =
    tr
      ( modulus-limit-∞-sequence-Preorder preorder-ℚ⁺)
      ( eq-htpy
        ( htpy-seq-geometric-sequence-ℚ⁺
          ( standard-geometric-sequence-ℚ⁺
            ( one-ℚ⁺)
            ( add-ℚ⁺
              ( one-ℚ⁺)
              ( le-diff-ℚ⁺
                ( one-ℚ⁺)
                ( common-ratio-geometric-sequence-ℚ⁺ u)
                ( 1<r))))
          ( u)
          ( is-one-init)
          ( right-diff-law-add-ℚ⁺
            ( one-ℚ⁺)
            ( common-ratio-geometric-sequence-ℚ⁺ u)
            ( 1<r))))
      ( modulus-limit-∞-standard-unitary-onep-geometric-sequence-ℚ⁺
        ( le-diff-ℚ⁺
          ( one-ℚ⁺)
          ( common-ratio-geometric-sequence-ℚ⁺ u)
          ( 1<r)))

  is-limit-∞-seq-unitary-geometric-sequence-ℚ⁺ :
    is-limit-∞-sequence-Preorder
      ( preorder-ℚ⁺)
      ( seq-geometric-sequence-ℚ⁺ u)
  is-limit-∞-seq-unitary-geometric-sequence-ℚ⁺ =
    unit-trunc-Prop modulus-limit-∞-seq-unitary-geometric-sequence-ℚ⁺
```

### A geometric sequence of positive rational numbers with initial term `1` and common ratio `r < 1` is a zero approximation

```agda
module _
  ( u : geometric-sequence-ℚ⁺)
  ( is-one-init : one-ℚ⁺ ＝ init-term-geometric-sequence-ℚ⁺ u)
  ( r<1 : le-ℚ⁺ (common-ratio-geometric-sequence-ℚ⁺ u) one-ℚ⁺)
  where

  modulus-zero-approximation-seq-unitary-geometric-sequence-ℚ⁺ :
    modulus-zero-approximation-sequence-ℚ⁺
      ( seq-geometric-sequence-ℚ⁺ u)
  modulus-zero-approximation-seq-unitary-geometric-sequence-ℚ⁺ =
    modulus-inv-modulus-limit-∞-sequence-ℚ⁺
      ( seq-geometric-sequence-ℚ⁺ u)
      ( modulus-limit-∞-seq-unitary-geometric-sequence-ℚ⁺
        ( inv-geometric-sequence-ℚ⁺ u)
        ( inv (inv-unit-Group group-mul-ℚ⁺) ∙
          ap inv-ℚ⁺ is-one-init)
        ( tr
          ( λ x → le-ℚ⁺ x (inv-ℚ⁺ (common-ratio-geometric-sequence-ℚ⁺ u)))
          ( inv-unit-Group group-mul-ℚ⁺)
          ( inv-le-ℚ⁺'
            ( common-ratio-geometric-sequence-ℚ⁺ u)
            ( one-ℚ⁺)
            ( r<1))))

  is-zero-approximation-seq-unitary-geometric-sequence-ℚ⁺ :
    is-zero-approximation-sequence-ℚ⁺ (seq-geometric-sequence-ℚ⁺ u)
  is-zero-approximation-seq-unitary-geometric-sequence-ℚ⁺ =
    unit-trunc-Prop modulus-zero-approximation-seq-unitary-geometric-sequence-ℚ⁺
```

## References

- [Bernoulli's inequality](https://en.wikipedia.org/wiki/Bernoulli%27s_inequality)
  at Wikipedia
