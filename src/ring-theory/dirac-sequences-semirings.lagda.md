# Dirac sequences in semirings

```agda
module ring-theory.dirac-sequences-semirings where
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
open import ring-theory.semirings
open import ring-theory.sequences-semirings
```

</details>

## Idea

The
{{#concept "Dirac sequences" Disambiguation="in a semiring" Agda=dirac-sequence-Semiring}}
in a [semiring](ring-theory.semirings.md) `R` is the family of
[sequences](ring-theory.sequences-semirings.md) `δ : ℕ → ℕ → R` such that

```text
  δ i i ＝ one-R
```

and, if `i ≠ j`,

```text
  δ i j = zero-ℝ
```

## Definition

### The dirac sequences in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  dirac-sequence-Semiring : ℕ → ℕ → type-Semiring R
  dirac-sequence-Semiring zero-ℕ zero-ℕ = one-Semiring R
  dirac-sequence-Semiring zero-ℕ (succ-ℕ j) = zero-Semiring R
  dirac-sequence-Semiring (succ-ℕ i) zero-ℕ = zero-Semiring R
  dirac-sequence-Semiring (succ-ℕ i) (succ-ℕ j) = dirac-sequence-Semiring i j
```

## Properties

### Dirac sequences are totally central

```agda
module _
  {l : Level} (R : Semiring l) (a : type-sequence-Semiring R)
  where abstract

  is-central-dirac-sequence-Semiring :
    (n : ℕ) → all-commute-sequence-Semiring R a (dirac-sequence-Semiring R n)
  is-central-dirac-sequence-Semiring zero-ℕ i zero-ℕ =
    right-unit-law-mul-Semiring R _ ∙ inv (left-unit-law-mul-Semiring R _)
  is-central-dirac-sequence-Semiring zero-ℕ i (succ-ℕ j) =
    right-zero-law-mul-Semiring R _ ∙ inv (left-zero-law-mul-Semiring R _)
  is-central-dirac-sequence-Semiring (succ-ℕ n) i zero-ℕ =
    right-zero-law-mul-Semiring R _ ∙ inv (left-zero-law-mul-Semiring R _)
  is-central-dirac-sequence-Semiring (succ-ℕ n) i (succ-ℕ j) =
    is-central-dirac-sequence-Semiring n i j
```
