# Monotonic sequences in partially ordered sets

```agda
module order-theory.monotonic-sequences-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.asymptotically-constant-sequences
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.subsequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.constant-sequences-posets
open import order-theory.decreasing-sequences-posets
open import order-theory.increasing-sequences-posets
open import order-theory.posets
open import order-theory.sequences-posets
```

</details>

## Idea

A [sequence in a partially ordered set](order-theory.sequences-posets.md) is
**monotonic** if it is [increasing](order-theory.increasing-sequences-posets.md)
or [decreasing](order-theory.decreasing-sequences-posets.md).

## Properties

### An increasing sequence in a partially ordered set with a decreasing subsequence is asymptotically constant

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {u : sequence-poset P}
  (H : is-increasing-sequence-poset P u)
  where

  ∞-constant-Σ-subsequence-decreasing-is-increasing-sequence-poset :
    Σ-subsequence (is-decreasing-sequence-poset P) u →
    is-∞-constant-sequence u
  ∞-constant-Σ-subsequence-decreasing-is-increasing-sequence-poset =
    ( ∞-constant-Σ-subsequence-constant-increasing-sequence-poset P H) ∘
    ( tot
      ( (constant-is-increasing-decreasing-sequence-poset P) ∘
        ( increasing-Π-subsequence-increasing-sequence-poset P u H)))
```

### A decreasing sequence in a partially ordered set with an increasing subsequence is asymptotically constant

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {u : sequence-poset P}
  (H : is-decreasing-sequence-poset P u)
  where

  ∞-constant-Σ-subsequence-increasing-is-decreasing-sequence-poset :
    Σ-subsequence (is-increasing-sequence-poset P) u →
    is-∞-constant-sequence u
  ∞-constant-Σ-subsequence-increasing-is-decreasing-sequence-poset =
    ( ∞-constant-Σ-subsequence-constant-decreasing-sequence-poset P H) ∘
    ( tot
      ( λ v K →
        constant-is-increasing-decreasing-sequence-poset
          ( P)
          ( K)
          ( decreasing-Π-subsequence-decreasing-sequence-poset P u H v)))
```
