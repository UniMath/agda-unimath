# Inequality of conatural numbers

```agda
{-# OPTIONS --guardedness #-}
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.inequality-conatural-numbers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.conatural-numbers funext univalence truncations

open import foundation.action-on-identifications-functions
open import foundation.binary-relations funext univalence truncations
open import foundation.cartesian-product-types funext univalence
open import foundation.coproduct-types funext univalence truncations
open import foundation.decidable-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.empty-types funext univalence truncations
open import foundation.function-types funext
open import foundation.functoriality-coproduct-types funext univalence truncations
open import foundation.identity-types funext
open import foundation.negation funext
open import foundation.propositions funext univalence
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.maybe

open import order-theory.posets funext univalence truncations
open import order-theory.preorders funext univalence truncations
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
