# Subsequences

```agda
module foundation.subsequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strictly-increasing-sequences-natural-numbers

open import foundation.function-types
open import foundation.identity-types
open import foundation.sequences
open import foundation.universe-levels
```

</details>

## Idea

A {{concept "subsequence" Agda=subsequence}} of a
[sequence](foundation.sequences.md) `u : ℕ → A` is a sequence `u ∘ f` for some
[strictly increasing](elementary-number-theory.strictly-increasing-sequences-natural-numbers.md)
sequence `f : ℕ → ℕ`.

## Definitions

### Subsequences

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  subsequence : UU lzero
  subsequence = strictly-increasing-sequence-ℕ
```

### The extracted sequence of a subsequence

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (v : subsequence u)
  where

  extract-subsequence : ℕ → ℕ
  extract-subsequence =
    seq-strictly-increasing-sequence-ℕ v

  is-strictly-increasing-extract-subsequence :
    is-strictly-increasing-sequence-ℕ extract-subsequence
  is-strictly-increasing-extract-subsequence =
    is-strictly-increasing-seq-strictly-increasing-sequence-ℕ v

  seq-subsequence : sequence A
  seq-subsequence n = u (extract-subsequence n)
```

## Properties

### Any sequence is a subsequence of itself

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  refl-subsequence : subsequence u
  refl-subsequence = strictly-increasing-id-ℕ

  compute-refl-subsequence : u ＝ seq-subsequence u refl-subsequence
  compute-refl-subsequence = refl
```

### A subsequence of a subsequence is a subsequence of the original sequence

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (v : subsequence u)
  (w : subsequence (seq-subsequence u v))
  where

  sub-subsequence : subsequence u
  sub-subsequence = comp-strictly-increasing-sequence-ℕ v w

  compute-sub-subsequence :
    Id
      (seq-subsequence u sub-subsequence)
      (seq-subsequence (seq-subsequence u v) w)
  compute-sub-subsequence = refl
```

### Subsequences are functorial

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (u : sequence A)
  where

  map-subsequence : subsequence u → subsequence (map-sequence f u)
  map-subsequence H = H
```

### The extracted sequence of the image of a subsequence is the extracted sequence of the image

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (u : sequence A)
  (v : subsequence u)
  where

  compute-map-subsequence :
    Id
      (map-sequence f (seq-subsequence u v))
      (seq-subsequence (map-sequence f u) (map-subsequence f u v))
  compute-map-subsequence = refl
```
