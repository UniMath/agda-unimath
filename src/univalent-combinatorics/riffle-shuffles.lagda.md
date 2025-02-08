# Riffle shuffles

```agda

module univalent-combinatorics.riffle-shuffles where

```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.inequality-standard-finite-types

open import foundation.automorphisms
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.propositions

open import order-theory.order-preserving-maps-posets

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

  is-shuffle-prop : (s : Fin p + Fin q ≃ Fin (p +ℕ q)) → Prop lzero
  is-shuffle-prop s = preserves-order-prop-Poset (Fin-Poset p) (Fin-Poset (p +ℕ q)) (map-equiv s ∘ inl) ∧ preserves-order-prop-Poset (Fin-Poset q) (Fin-Poset (p +ℕ q)) (map-equiv s ∘ inr)

  is-shuffle : (s : Fin p + Fin q ≃ Fin (p +ℕ q)) → UU lzero
  is-shuffle s = type-Prop (is-shuffle-prop s)

  shuffle : UU lzero
  shuffle = Σ (Fin p + Fin q ≃ Fin (p +ℕ q)) λ s → is-shuffle s
```
