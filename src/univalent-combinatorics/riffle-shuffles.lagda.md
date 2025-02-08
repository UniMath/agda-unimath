# Riffle shuffles

```agda
module univalent-combinatorics.riffle-shuffles where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.automorphisms
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.propositions

open import order-theory.order-preserving-maps-posets
open import order-theory.posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We show how to shuffle cards. A **`(p , q)`-riffle shuffle** of the
[standard finite type](univalent-combinatorics.standard-finite-types.md)
`Fin (p +ℕ q)` is an [equivalence](foundation.equivalences)
`s : Fin p + Fin q ≃ Fin (p +ℕ q)` such that the compositions
`map-equiv s ∘ inl, map-equiv s ∘ inr` are
[monotone](order-theory.order-preserving-maps-posets).

## Definition

```agda
module _
  (p q : ℕ)
  where
  left-deck : Poset lzero lzero
  left-deck = Fin-Poset p

  right-deck : Poset lzero lzero
  right-deck = Fin-Poset q

  full-deck : Poset lzero lzero
  full-deck = Fin-Poset (p +ℕ q)

  is-shuffle-prop-left : (s : Fin p + Fin q ≃ Fin (p +ℕ q)) → Prop lzero
  is-shuffle-prop-left s =
    preserves-order-prop-Poset left-deck full-deck (map-equiv s ∘ inl)

  is-shuffle-prop-right : (s : Fin p + Fin q ≃ Fin (p +ℕ q)) → Prop lzero
  is-shuffle-prop-right s =
    preserves-order-prop-Poset right-deck full-deck (map-equiv s ∘ inr)

  is-shuffle-prop : (s : Fin p + Fin q ≃ Fin (p +ℕ q)) → Prop lzero
  is-shuffle-prop s = is-shuffle-prop-left s ∧ is-shuffle-prop-right s

  is-shuffle : (s : Fin p + Fin q ≃ Fin (p +ℕ q)) → UU lzero
  is-shuffle s = type-Prop (is-shuffle-prop s)

  shuffle : UU lzero
  shuffle = Σ (Fin p + Fin q ≃ Fin (p +ℕ q)) λ s → is-shuffle s
```
