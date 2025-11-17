# Monotonic sequences in posets

```agda
module order-theory.monotonic-sequences-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences

open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

A
{{#concept "monotonic sequence" Agda=monotonic-sequence-Poset Disambiguation="in a poset"}}
in a [poset](order-theory.posets.md) `P` is a [sequence](lists.sequences.md)
`aₙ` such that whenever `m ≤ n`, `aₘ ≤ aₙ`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  is-monotonic-prop-sequence-Poset : subtype l2 (sequence (type-Poset P))
  is-monotonic-prop-sequence-Poset a = preserves-order-prop-Poset ℕ-Poset P a

  is-monotonic-sequence-Poset : sequence (type-Poset P) → UU l2
  is-monotonic-sequence-Poset a = type-Prop (is-monotonic-prop-sequence-Poset a)
```

## Properties

### If `aₙ ≤ aₙ₊₁` for all `n`, then the sequence `aₙ` is monotonic

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  abstract
    is-monotonic-sequence-is-increasing-Poset :
      (a : sequence (type-Poset P)) →
      ((n : ℕ) → leq-Poset P (a n) (a (succ-ℕ n))) →
      is-monotonic-sequence-Poset P a
    is-monotonic-sequence-is-increasing-Poset a H m n m≤n =
      let
        (l , l+m=n) = subtraction-leq-ℕ m n m≤n
      in
        tr
          ( λ k → leq-Poset P (a m) (a k))
          ( commutative-add-ℕ m l ∙ l+m=n)
          ( lemma l)
      where
        lemma : (k : ℕ) → leq-Poset P (a m) (a (m +ℕ k))
        lemma 0 = refl-leq-Poset P (a m)
        lemma (succ-ℕ k) =
          transitive-leq-Poset P
            ( a m)
            ( a (m +ℕ k))
            ( a (m +ℕ succ-ℕ k))
            ( H (m +ℕ k))
            ( lemma k)
```
