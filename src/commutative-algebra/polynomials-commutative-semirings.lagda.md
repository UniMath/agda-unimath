# Polynomials in commutative semirings

```agda
module commutative-algebra.polynomials-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.formal-power-series-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "polynomial" WDID=Q43260 WD="polynomial" disambiguation="in a commutative semiring" Agda=polynomial-Commutative-Semiring}}
in a [commutative semiring](commutative-algebra.commutative-semirings.md) is a
[formal power series](commutative-algebra.formal-power-series-commutative-semirings.md)
`Σₙ aₙxⁿ` whose coefficients `aₙ` are zero for sufficiently large `n`.

## Definition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  is-polynomial-prop-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R → Prop l
  is-polynomial-prop-formal-power-series-Commutative-Semiring
    (formal-power-series-coefficients-Commutative-Semiring a) =
      ∃ ( ℕ)
        ( λ N →
          Π-Prop ℕ (λ n → is-zero-prop-Commutative-Semiring R (a (n +ℕ N))))

  is-polynomial-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R → UU l
  is-polynomial-formal-power-series-Commutative-Semiring a =
    type-Prop (is-polynomial-prop-formal-power-series-Commutative-Semiring a)

  polynomial-Commutative-Semiring : UU l
  polynomial-Commutative-Semiring =
    type-subtype is-polynomial-prop-formal-power-series-Commutative-Semiring
```

## Properties

### The zero polynomial

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  zero-polynomial-Commutative-Semiring : polynomial-Commutative-Semiring R
  zero-polynomial-Commutative-Semiring =
    ( zero-formal-power-series-Commutative-Semiring R ,
      intro-exists zero-ℕ (λ _ → refl))
```

### The one polynomial

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  one-polynomial-Commutative-Semiring : polynomial-Commutative-Semiring R
  one-polynomial-Commutative-Semiring =
    ( one-formal-power-series-Commutative-Semiring R ,
      intro-exists 1 (λ _ → refl))
```

### The identity polynomial

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  id-polynomial-Commutative-Semiring : polynomial-Commutative-Semiring R
  id-polynomial-Commutative-Semiring =
    ( id-formal-power-series-Commutative-Semiring R ,
      intro-exists 2 (λ _ → refl))
```

### The set of polynomials

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  set-polynomial-Commutative-Semiring : Set l
  set-polynomial-Commutative-Semiring =
    set-subset
      ( set-formal-power-series-Commutative-Semiring R)
      ( is-polynomial-prop-formal-power-series-Commutative-Semiring R)
```
