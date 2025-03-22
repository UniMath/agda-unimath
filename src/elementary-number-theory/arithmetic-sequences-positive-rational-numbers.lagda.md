# Arithmetic sequences of positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.arithmetic-sequences-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.archimedean-property-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.sequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.powers-of-elements-monoids
```

</details>

## Idea

The
{{#concept "arithmetic sequence" Disambiguation="of positive rational numbers" Agda=arithmetic-sequence-ℚ⁺ WD="arithmetic progression" WDID=Q170008}}
of positive rational numbers with initial term `(a : ℚ⁺)` and common difference
`(d : ℚ⁺)` is the sequence `u : ℕ → ℚ⁺` characterized by

- `u₀ = a`
- `∀ (n : ℕ) uₙ₊₁ = uₙ + d`.

The terms of an arithmetic sequence of positive rational numbers have no greater
element.

## Definitions

### Preliminary definition

```agda
module _
  (d : ℚ⁺)
  where

  power-add-ℚ⁺ : sequence ℚ
  power-add-ℚ⁺ n = power-Monoid monoid-add-ℚ n (rational-ℚ⁺ d)

  abstract
    lemma-leq-power-add-ℚ⁺ :
      (n : ℕ) → leq-ℚ zero-ℚ (power-add-ℚ⁺ n)
    lemma-leq-power-add-ℚ⁺ zero-ℕ = refl-leq-ℚ zero-ℚ
    lemma-leq-power-add-ℚ⁺ (succ-ℕ n) =
        transitive-leq-ℚ
          ( zero-ℚ)
          ( power-Monoid monoid-add-ℚ n (rational-ℚ⁺ d))
          ( power-Monoid monoid-add-ℚ (succ-ℕ n) (rational-ℚ⁺ d))
          ( inv-tr
              ( leq-ℚ (power-add-ℚ⁺ n))
              ( power-succ-Monoid monoid-add-ℚ n (rational-ℚ⁺ d))
              ( leq-le-ℚ
                { power-add-ℚ⁺ n}
                {add-ℚ (power-add-ℚ⁺ n) (rational-ℚ⁺ d)}
                ( le-right-add-rational-ℚ⁺
                  ( power-add-ℚ⁺ n)
                  ( d))))
          ( lemma-leq-power-add-ℚ⁺ n)
```

### The arithmetic sequences associated to an initial term and a common difference

```agda
module _
  (a d : ℚ⁺)
  where

  rational-arithmetic-sequence-ℚ⁺ : sequence ℚ
  rational-arithmetic-sequence-ℚ⁺ = add-ℚ (rational-ℚ⁺ a) ∘ power-add-ℚ⁺ d

  abstract
    is-positive-rational-arithmetic-sequence-ℚ⁺ :
      (n : ℕ) → is-positive-ℚ (rational-arithmetic-sequence-ℚ⁺ n)
    is-positive-rational-arithmetic-sequence-ℚ⁺ n =
      is-positive-le-zero-ℚ
        ( (rational-ℚ⁺ a) +ℚ (power-add-ℚ⁺ d n))
        ( concatenate-leq-le-ℚ
          ( zero-ℚ)
          ( power-Monoid monoid-add-ℚ n (rational-ℚ⁺ d))
          ( rational-ℚ⁺ a +ℚ power-Monoid monoid-add-ℚ n (rational-ℚ⁺ d))
          ( lemma-leq-power-add-ℚ⁺ d n)
          ( le-left-add-rational-ℚ⁺
            ( power-Monoid monoid-add-ℚ n (rational-ℚ⁺ d))
            ( a)))

  arithmetic-sequence-ℚ⁺ : sequence ℚ⁺
  arithmetic-sequence-ℚ⁺ n =
    ( rational-arithmetic-sequence-ℚ⁺ n) ,
    ( is-positive-rational-arithmetic-sequence-ℚ⁺ n)
```

### Unitary arithmetic sequences of positive rational numbers

An arithmetic sequence with initial term equal to `1` is called unitary

```agda
module _
  (d : ℚ⁺)
  where

  unitary-arithmetic-sequence-ℚ⁺ : sequence ℚ⁺
  unitary-arithmetic-sequence-ℚ⁺ = arithmetic-sequence-ℚ⁺ one-ℚ⁺ d
```

## Properties

### `u₀ = a`

```agda
module _
  (a d : ℚ⁺)
  where

  abstract
    eq-init-arithmetic-sequence-ℚ⁺ :
      arithmetic-sequence-ℚ⁺ a d zero-ℕ ＝ a
    eq-init-arithmetic-sequence-ℚ⁺ =
      eq-ℚ⁺ (right-unit-law-add-ℚ (rational-ℚ⁺ a))
```

### `uₙ₊₁ = uₙ + d`

```agda
module _
  (a d : ℚ⁺)
  where

  abstract
    eq-succ-arithmetic-sequence-ℚ⁺ :
      ( n : ℕ) →
      ( arithmetic-sequence-ℚ⁺ a d (succ-ℕ n)) ＝
      ( arithmetic-sequence-ℚ⁺ a d n +ℚ⁺ d)
    eq-succ-arithmetic-sequence-ℚ⁺ n =
      eq-ℚ⁺
        ( ( ap
            ( add-ℚ (rational-ℚ⁺ a))
            ( power-succ-Monoid monoid-add-ℚ n (rational-ℚ⁺ d))) ∙
          ( inv
            (associative-add-ℚ
              ( rational-ℚ⁺ a)
              ( power-add-ℚ⁺ d n)
              ( rational-ℚ⁺ d))))
```

### The nth term of an arithmetic sequence with initial term `a` and common difference `d` is `a + n d`

```agda
module _
  (a d : ℚ⁺) (n : ℕ)
  where

  abstract
    compute-arithmetic-sequence-ℚ⁺ :
      ( rational-ℚ⁺ a +ℚ rational-ℕ n *ℚ rational-ℚ⁺ d) ＝
      ( rational-arithmetic-sequence-ℚ⁺ a d n)
    compute-arithmetic-sequence-ℚ⁺ =
      ap
        ( add-ℚ (rational-ℚ⁺ a))
        ( compute-power-monoid-add-ℚ n (rational-ℚ⁺ d))
```

### An arithmetic sequence of positive rational numbers is strictly increasing

```agda
module _
  (a d : ℚ⁺) (n : ℕ)
  where

  abstract
    is-strictly-increasing-arithmetic-sequence-ℚ⁺ :
      le-ℚ⁺
        ( arithmetic-sequence-ℚ⁺ a d n)
        ( arithmetic-sequence-ℚ⁺ a d (succ-ℕ n))
    is-strictly-increasing-arithmetic-sequence-ℚ⁺ =
      inv-tr
        ( le-ℚ⁺ (arithmetic-sequence-ℚ⁺ a d n))
        ( eq-succ-arithmetic-sequence-ℚ⁺ a d n)
        ( le-right-add-rational-ℚ⁺
          ( rational-ℚ⁺ (arithmetic-sequence-ℚ⁺ a d n))
          ( d))
```

### The terms of an arithmetic sequence of positive rational numbers are greater than or equal to its initial term

```agda
module _
  (a d : ℚ⁺)
  where

  abstract
    leq-init-arithmetic-sequence-ℚ⁺ :
      (n : ℕ) → leq-ℚ⁺ a (arithmetic-sequence-ℚ⁺ a d n)
    leq-init-arithmetic-sequence-ℚ⁺ zero-ℕ =
      inv-tr
        ( leq-ℚ⁺ a)
        ( eq-init-arithmetic-sequence-ℚ⁺ a d)
        ( refl-leq-ℚ (rational-ℚ⁺ a))
    leq-init-arithmetic-sequence-ℚ⁺ (succ-ℕ n) =
      transitive-leq-ℚ
        ( rational-ℚ⁺ a)
        ( rational-ℚ⁺ (arithmetic-sequence-ℚ⁺ a d n))
        ( rational-ℚ⁺ (arithmetic-sequence-ℚ⁺ a d (succ-ℕ n)))
        ( leq-le-ℚ
          { rational-ℚ⁺ (arithmetic-sequence-ℚ⁺ a d n)}
          { rational-ℚ⁺ (arithmetic-sequence-ℚ⁺ a d (succ-ℕ n))}
          ( is-strictly-increasing-arithmetic-sequence-ℚ⁺ a d n))
        ( leq-init-arithmetic-sequence-ℚ⁺ n)
```

### An arithmetic sequence of positive rational numbers has no upper bound

```agda
module _
  (a d : ℚ⁺)
  where

  is-unbounded-arithmetic-sequence-ℚ⁺ :
    (M : ℚ⁺) → Σ ℕ (le-ℚ⁺ M ∘ arithmetic-sequence-ℚ⁺ a d)
  is-unbounded-arithmetic-sequence-ℚ⁺ M =
    tot
      ( tr-archimidean-bound)
      ( bound-archimedean-property-ℚ
        ( rational-ℚ⁺ d)
        ( rational-ℚ⁺ M)
        ( is-positive-rational-ℚ⁺ d))
    where

      tr-archimidean-bound :
        (n : ℕ) (I : le-ℚ (rational-ℚ⁺ M) (rational-ℕ n *ℚ (rational-ℚ⁺ d))) →
        le-ℚ⁺ M (arithmetic-sequence-ℚ⁺ a d n)
      tr-archimidean-bound n I =
        tr
          ( le-ℚ (rational-ℚ⁺ M))
          ( compute-arithmetic-sequence-ℚ⁺ a d n)
          ( transitive-le-ℚ
            ( rational-ℚ⁺ M)
            ( rational-ℕ n *ℚ rational-ℚ⁺ d)
            ( (rational-ℚ⁺ a) +ℚ rational-ℕ n *ℚ rational-ℚ⁺ d)
            ( le-left-add-rational-ℚ⁺
              ( rational-ℕ n *ℚ rational-ℚ⁺ d)
              ( a))
            ( I))
```

### The ratio of two consecutive terms of a unitary arithmetic sequence is bounded

The terms of a unitary arithmetic sequence with common difference `d` satisfy
`uₙ₊₁/uₙ ≤ 1 + d`; we prove the equivalent inequality `uₙ₊₁ ≤ uₙ (1 + d)`.

```agda
module _
  (d : ℚ⁺)
  where

  abstract
    bounded-ratio-unitary-arithmetic-sequence-ℚ⁺ :
      (n : ℕ) →
      leq-ℚ⁺
        ( unitary-arithmetic-sequence-ℚ⁺ d (succ-ℕ n))
        ( mul-ℚ⁺
          ( unitary-arithmetic-sequence-ℚ⁺ d n)
          ( one-ℚ⁺ +ℚ⁺ d))
    bounded-ratio-unitary-arithmetic-sequence-ℚ⁺ n =
      binary-tr
        ( leq-ℚ⁺)
        ( inv (eq-succ-arithmetic-sequence-ℚ⁺ one-ℚ⁺ d n))
        ( inv rhs)
        ( H)
      where

        rhs :
          ( mul-ℚ⁺
            ( unitary-arithmetic-sequence-ℚ⁺ d n)
            ( one-ℚ⁺ +ℚ⁺ d)) ＝
          ( add-ℚ⁺
            ( unitary-arithmetic-sequence-ℚ⁺ d n)
            ( unitary-arithmetic-sequence-ℚ⁺ d n *ℚ⁺ d))
        rhs =
          eq-ℚ⁺
            ( ( left-distributive-mul-add-ℚ
                ( rational-arithmetic-sequence-ℚ⁺ one-ℚ⁺ d n)
                ( one-ℚ)
                ( rational-ℚ⁺ d)) ∙
              ( ap
                ( λ x →
                  add-ℚ
                    ( x)
                    ( mul-ℚ
                      ( rational-arithmetic-sequence-ℚ⁺ one-ℚ⁺ d n)
                      ( rational-ℚ⁺ d)))
                ( right-unit-law-mul-ℚ
                  (rational-arithmetic-sequence-ℚ⁺ one-ℚ⁺ d n))))
        H :
          leq-ℚ⁺
            ( add-ℚ⁺
              ( unitary-arithmetic-sequence-ℚ⁺ d n)
              ( d))
          ( add-ℚ⁺
            ( unitary-arithmetic-sequence-ℚ⁺ d n)
            ( unitary-arithmetic-sequence-ℚ⁺ d n *ℚ⁺ d))
        H =
          preserves-leq-right-add-ℚ
            ( rational-arithmetic-sequence-ℚ⁺ one-ℚ⁺ d n)
            ( rational-ℚ⁺ d)
            ( rational-arithmetic-sequence-ℚ⁺ one-ℚ⁺ d n *ℚ rational-ℚ⁺ d)
            ( tr
              ( λ x →
                leq-ℚ
                  ( x)
                  ( mul-ℚ
                    ( rational-arithmetic-sequence-ℚ⁺ one-ℚ⁺ d n)
                    ( rational-ℚ⁺ d)))
              ( left-unit-law-mul-ℚ (rational-ℚ⁺ d))
              ( preserves-leq-right-mul-ℚ⁺
                ( d)
                ( one-ℚ)
                ( rational-arithmetic-sequence-ℚ⁺ one-ℚ⁺ d n)
                ( leq-init-arithmetic-sequence-ℚ⁺ one-ℚ⁺ d n)))
```

## References

- [Arithmetic progressions](https://en.wikipedia.org/wiki/Arithmetic_progression)
  at Wikipedia
