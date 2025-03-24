# Riffle shuffles

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module univalent-combinatorics.riffle-shuffles
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-standard-finite-types funext univalence truncations
open import elementary-number-theory.natural-numbers

open import foundation.automorphisms funext univalence
open import foundation.conjunction funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.propositions

open import order-theory.order-preserving-maps-posets funext univalence truncations
open import order-theory.posets funext univalence truncations

open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Idea

A
`(p , q)`-{{#concept "riffle shuffle" Disambiguation="on standard finite types" Agda=riffle-shuffle-Fin}}
of the [standard finite type](univalent-combinatorics.standard-finite-types.md)
`Fin (p +ℕ q)` is an [equivalence](foundation-core.equivalences.md)
`s : Fin p + Fin q ≃ Fin (p +ℕ q)` such that the compositions
`map-equiv s ∘ inl, map-equiv s ∘ inr` are
[monotone](order-theory.order-preserving-maps-posets.md).

## Definitions

### Riffle shuffles on standard finite types

```agda
module _
  (p q : ℕ)
  where

  is-left-riffle-shuffle-prop-Fin :
    (s : Fin p + Fin q ≃ Fin (p +ℕ q)) → Prop lzero
  is-left-riffle-shuffle-prop-Fin s =
    preserves-order-prop-Poset
      ( Fin-Poset p)
      ( Fin-Poset (p +ℕ q))
      ( map-equiv s ∘ inl)

  is-right-riffle-shuffle-prop-Fin :
    (s : Fin p + Fin q ≃ Fin (p +ℕ q)) → Prop lzero
  is-right-riffle-shuffle-prop-Fin s =
    preserves-order-prop-Poset
      ( Fin-Poset q)
      ( Fin-Poset (p +ℕ q))
      ( map-equiv s ∘ inr)

  is-riffle-shuffle-prop-Fin : (s : Fin p + Fin q ≃ Fin (p +ℕ q)) → Prop lzero
  is-riffle-shuffle-prop-Fin s =
    is-left-riffle-shuffle-prop-Fin s ∧ is-right-riffle-shuffle-prop-Fin s

  is-riffle-shuffle-Fin : (s : Fin p + Fin q ≃ Fin (p +ℕ q)) → UU lzero
  is-riffle-shuffle-Fin s = type-Prop (is-riffle-shuffle-prop-Fin s)

  riffle-shuffle-Fin : UU lzero
  riffle-shuffle-Fin = Σ (Fin p + Fin q ≃ Fin (p +ℕ q)) (is-riffle-shuffle-Fin)
```
