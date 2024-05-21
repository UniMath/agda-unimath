# Subsequences

```agda
module foundation.subsequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.monotonic-sequences-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.asymptotical-dependent-sequences
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

A **subsequence** of a [sequence](foundation.sequences.md) `u : ℕ → A` is a
sequence `u ∘ f` for some
[strictly increasing](elementary-number-theory.monotonic-sequences-natural-numbers.md)
map `f : ℕ → ℕ`.

## Definition

### Subsequences

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  subsequence : UU lzero
  subsequence = type-subtype is-strictly-increasing-sequence-prop-ℕ
```

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (v : subsequence u)
  where

  extract-subsequence : ℕ → ℕ
  extract-subsequence = pr1 v

  is-strictly-increasing-extract-subsequence :
    is-strictly-increasing-sequence-ℕ extract-subsequence
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

  eq-refl-subsequence : u ＝ sequence-subsequence u refl-subsequence
  eq-refl-subsequence = refl
```

### The subsequence that skips the first term

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  skip-zero-sequence : subsequence u
  skip-zero-sequence = (succ-ℕ , λ i j K → K)

  eq-skip-zero-sequence :
    u ∘ succ-ℕ ＝ sequence-subsequence u skip-zero-sequence
  eq-skip-zero-sequence = refl
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
      (map-sequence f (sequence-subsequence u v))
      (sequence-subsequence (map-sequence f u) (map-subsequence f u v))
  compute-map-subsequence = refl
```

### Modulus of a subsquence

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (v : subsequence u)
  where

  modulus-subsequence : ℕ → ℕ
  modulus-subsequence =
    modulus-limit-∞-is-strictly-increasing-sequence-ℕ
      ( extract-subsequence u v)
      ( is-strictly-increasing-extract-subsequence u v)

  is-modulus-subsequence :
    (N p : ℕ) →
    leq-ℕ (modulus-subsequence N) p →
    leq-ℕ N (extract-subsequence u v p)
  is-modulus-subsequence =
    is-modulus-limit-∞-is-strictly-increasing-sequence-ℕ
      ( extract-subsequence u v)
      ( is-strictly-increasing-extract-subsequence u v)
```

### A dependent sequence is asymptotical if and only if all its subsequences are asymptotical

```agda
module _
  {l : Level} (A : ℕ → UU l)
  where

  asymptotically-sequence-subsequence :
    asymptotically A →
    ((B : subsequence A) → asymptotically (sequence-subsequence A B))
  asymptotically-sequence-subsequence H B =
    map-Σ
      ( is-modulus-dependent-sequence (sequence-subsequence A B))
      ( modulus-subsequence A B)
      ( λ N K p I →
        K
          ( extract-subsequence A B p)
          ( is-modulus-subsequence A B N p I))
      ( H)

  asymptotically-subsequence :
    ((B : subsequence A) → asymptotically (sequence-subsequence A B)) →
    asymptotically A
  asymptotically-subsequence H = H (refl-subsequence A)
```
