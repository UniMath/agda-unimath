# Strictly ordered pairs of natural numbers

```agda
module elementary-number-theory.strictly-preordered-pairs-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.pairs-of-distinct-elements
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A strictly ordered pair of natural numbers consists of `x y : ℕ` such that
`x < y`.

## Definition

```agda
strictly-preordered-pair-ℕ : UU lzero
strictly-preordered-pair-ℕ = Σ ℕ (λ x → Σ ℕ (λ y → le-ℕ x y))

module _
  (p : strictly-preordered-pair-ℕ)
  where

  first-strictly-preordered-pair-ℕ : ℕ
  first-strictly-preordered-pair-ℕ = pr1 p

  second-strictly-preordered-pair-ℕ : ℕ
  second-strictly-preordered-pair-ℕ = pr1 (pr2 p)

  strict-inequality-strictly-preordered-pair-ℕ :
    le-ℕ first-strictly-preordered-pair-ℕ second-strictly-preordered-pair-ℕ
  strict-inequality-strictly-preordered-pair-ℕ = pr2 (pr2 p)
```

## Properties

### Strictly ordered pairs of natural numbers are pairs of distinct elements

```agda
pair-of-distinct-elements-strictly-preordered-pair-ℕ :
  strictly-preordered-pair-ℕ → pair-of-distinct-elements ℕ
pair-of-distinct-elements-strictly-preordered-pair-ℕ (a , b , H) =
  (a , b , neq-le-ℕ H)
```

### Any pair of distinct elements of natural numbers can be strictly ordered

```agda
strictly-preordered-pair-pair-of-distinct-elements-ℕ' :
  (a b : ℕ) → a ≠ b → strictly-preordered-pair-ℕ
strictly-preordered-pair-pair-of-distinct-elements-ℕ' zero-ℕ zero-ℕ H =
  ex-falso (H refl)
strictly-preordered-pair-pair-of-distinct-elements-ℕ' zero-ℕ (succ-ℕ b) H =
  (0 , succ-ℕ b , star)
strictly-preordered-pair-pair-of-distinct-elements-ℕ' (succ-ℕ a) zero-ℕ H =
  (0 , succ-ℕ a , star)
strictly-preordered-pair-pair-of-distinct-elements-ℕ' (succ-ℕ a) (succ-ℕ b) H =
  map-Σ
    ( λ x → Σ ℕ (λ y → le-ℕ x y))
    ( succ-ℕ)
    ( λ x →
      map-Σ (le-ℕ (succ-ℕ x)) succ-ℕ (λ y → id))
    ( strictly-preordered-pair-pair-of-distinct-elements-ℕ' a b
      ( λ p → H (ap succ-ℕ p)))

strictly-preordered-pair-pair-of-distinct-elements-ℕ :
  pair-of-distinct-elements ℕ → strictly-preordered-pair-ℕ
strictly-preordered-pair-pair-of-distinct-elements-ℕ (a , b , H) =
  strictly-preordered-pair-pair-of-distinct-elements-ℕ' a b H
```
