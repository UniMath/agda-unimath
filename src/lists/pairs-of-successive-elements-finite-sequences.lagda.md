# Pairs of successive elements in a finite sequence

```agda
module lists.pairs-of-successive-elements-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a nonempty [finite sequence](lists.finite-sequences.md) `a` with elements
`a₀, a₁, ..., aₙ`, the
{{#concept "sequence of pairs of successive elements" Agda=pair-succ-fin-sequence}}
of `a` is the the sequence `(a₀, a₁), (a₁, a₂), ..., (aₙ₋₁, aₙ)`.

## Definition

```agda
pair-succ-fin-sequence :
  {l : Level} {A : UU l} (n : ℕ) →
  fin-sequence A (succ-ℕ n) → fin-sequence (A × A) n
pair-succ-fin-sequence n a i =
  ( a (skip-zero-Fin n i) ,
    a (inl-Fin n i))
```
