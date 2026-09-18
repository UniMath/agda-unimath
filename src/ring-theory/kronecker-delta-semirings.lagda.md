# Kronecker delta sequences in semirings

```agda
module ring-theory.kronecker-delta-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.commuting-elements-monoids
open import group-theory.semigroups

open import ring-theory.function-semirings
open import ring-theory.mutually-centralizing-sequences-semirings
open import ring-theory.semirings
open import ring-theory.sequences-semirings
```

</details>

## Idea

The
{{#concept "Kronecker delta sequence" Disambiguation="in a semiring" Agda=kronecker-delta-Semiring WD="Kronecker delta" WDID=Q192826}}
at `i : ℕ` in a [semiring](ring-theory.semirings.md) `R` is the
[sequence](ring-theory.sequences-semirings.md) `δᵢ : ℕ → R` such that

```text
  δᵢ i ＝ 1
```

and `δᵢ j ＝ 0` whenever `i ≠ j`. In other words, `δᵢ` is the sequence whose
`i`-th entry is `1` and whose other entries are `0`.

## Definition

### The Kronecker delta sequence in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  kronecker-delta-Semiring : ℕ → ℕ → type-Semiring R
  kronecker-delta-Semiring zero-ℕ zero-ℕ = one-Semiring R
  kronecker-delta-Semiring zero-ℕ (succ-ℕ j) = zero-Semiring R
  kronecker-delta-Semiring (succ-ℕ i) zero-ℕ = zero-Semiring R
  kronecker-delta-Semiring (succ-ℕ i) (succ-ℕ j) = kronecker-delta-Semiring i j
```

## Properties

### Kronecker delta sequences are mutually centralizing with all sequences

```agda
module _
  {l : Level} (R : Semiring l) (a : type-sequence-Semiring R)
  where abstract

  is-mutually-centralizing-kronecker-delta-Semiring :
    (n : ℕ) →
    is-mutually-centralizing-sequence-Semiring
      ( R)
      ( a)
      (kronecker-delta-Semiring R n)
  is-mutually-centralizing-kronecker-delta-Semiring zero-ℕ i zero-ℕ =
    right-unit-law-mul-Semiring R _ ∙ inv (left-unit-law-mul-Semiring R _)
  is-mutually-centralizing-kronecker-delta-Semiring zero-ℕ i (succ-ℕ j) =
    right-zero-law-mul-Semiring R _ ∙ inv (left-zero-law-mul-Semiring R _)
  is-mutually-centralizing-kronecker-delta-Semiring (succ-ℕ n) i zero-ℕ =
    right-zero-law-mul-Semiring R _ ∙ inv (left-zero-law-mul-Semiring R _)
  is-mutually-centralizing-kronecker-delta-Semiring (succ-ℕ n) i (succ-ℕ j) =
    is-mutually-centralizing-kronecker-delta-Semiring n i j
```

## External links

- [Kronecker delta](https://en.wikipedia.org/wiki/Kronecker_delta) at Wikipedia
