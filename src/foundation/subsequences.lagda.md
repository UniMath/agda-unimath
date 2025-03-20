# Subsequences

```agda
module foundation.subsequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.monotonic-endomaps-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "subsequence" Agda=subsequence Disambiguation="of a sequence"}} of
a [sequence](foundation.sequences.md) `u : ℕ → A` is a sequence `u ∘ f` for some
[strictly increasing](elementary-number-theory.monotonic-endomaps-natural-numbers.md)
map `f : ℕ → ℕ`.

## Definition

### Subsequences

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  subsequence : UU lzero
  subsequence = type-subtype is-strictly-increasing-endomap-prop-ℕ
```

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (v : subsequence u)
  where

  extract-subsequence : ℕ → ℕ
  extract-subsequence = pr1 v

  is-strictly-increasing-extract-subsequence :
    is-strictly-increasing-endomap-ℕ extract-subsequence
  is-strictly-increasing-extract-subsequence = pr2 v

  sequence-subsequence : sequence A
  sequence-subsequence n = u (extract-subsequence n)
```

## Properties

### Any sequence is a subsequence of itself

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  refl-subsequence : subsequence u
  refl-subsequence = (id , λ i j → id)

  eq-refl-subsequence : sequence-subsequence u refl-subsequence ＝ u
  eq-refl-subsequence = refl
```

### A subsequence of a subsequence is a subsequence of the original sequence

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (v : subsequence u)
  (w : subsequence (sequence-subsequence u v))
  where

  sub-subsequence : subsequence u
  pr1 sub-subsequence =
    extract-subsequence u v ∘ extract-subsequence (sequence-subsequence u v) w
  pr2 sub-subsequence i j H =
    is-strictly-increasing-extract-subsequence u v
      ( extract-subsequence (sequence-subsequence u v) w i)
      ( extract-subsequence (sequence-subsequence u v) w j)
      ( is-strictly-increasing-extract-subsequence
        ( sequence-subsequence u v)
        ( w)
        ( i)
        ( j)
        ( H))

  eq-sub-subsequence :
    Id
      (sequence-subsequence u sub-subsequence)
      (sequence-subsequence (sequence-subsequence u v) w)
  eq-sub-subsequence = refl
```
