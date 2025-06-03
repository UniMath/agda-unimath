# Inequality of conatural numbers

```agda
{-# OPTIONS --guardedness #-}

module elementary-number-theory.inequality-conatural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.conatural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.maybe
open import foundation.negation
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

The
{{#concept "inequality relation" Disambiguation="on conatural numbers" Agda=_≤-ℕ∞_}}
`≤` on the [conatural numbers](elementary-number-theory.conatural-numbers.md) is
the unique coinductively defined relation such that `0` is less than any
conatural number, and such that `m+1 ≤ n+1`
[if and only if](foundation.logical-equivalences.md) `m ≤ n`.

## Definitions

### Inequality on the conatural numbers

```agda
record leq-ℕ∞ (x y : ℕ∞) : UU lzero

leq-Maybe-ℕ∞ : Maybe ℕ∞ → Maybe ℕ∞ → UU lzero
leq-Maybe-ℕ∞ (inl x) (inl y) = leq-ℕ∞ x y
leq-Maybe-ℕ∞ (inl x) (inr y) = empty
leq-Maybe-ℕ∞ (inr x) y = unit

record leq-ℕ∞ x y where
  coinductive
  constructor cons-leq-ℕ∞
  field
    decons-leq-ℕ∞ : leq-Maybe-ℕ∞ (decons-ℕ∞ x) (decons-ℕ∞ y)

infix 30 _≤-ℕ∞_
_≤-ℕ∞_ = leq-ℕ∞
```
