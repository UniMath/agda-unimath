# Eventually constant sequences

```agda
module foundation.eventually-constant-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.monotonic-sequences-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.eventually-equal-sequences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.sequences
open import foundation.subsequences
open import foundation.universe-levels
```

</details>

## Idea

A [sequence](foundation.sequences.md) `u` is
{{#concept "eventually constant" Agda=is-eventually-constant-sequence}} if
`u p ＝ u q` for sufficiently large `p` and `q`.

## Definition

### Eventually constant sequences

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  is-modulus-eventually-constant-sequence : (N : ℕ) → UU l
  is-modulus-eventually-constant-sequence N =
    (p q : ℕ) → leq-ℕ N p → leq-ℕ N q → (u p) ＝ (u q)

  is-eventually-constant-sequence : UU l
  is-eventually-constant-sequence =
    Σ ℕ is-modulus-eventually-constant-sequence
```

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  (H : is-eventually-constant-sequence u)
  where

  modulus-eventually-constant-sequence : ℕ
  modulus-eventually-constant-sequence = pr1 H

  is-modulus-modulus-eventually-constant-sequence :
    is-modulus-eventually-constant-sequence
      u
      modulus-eventually-constant-sequence
  is-modulus-modulus-eventually-constant-sequence = pr2 H

  value-eventually-constant-sequence : A
  value-eventually-constant-sequence =
    u modulus-eventually-constant-sequence
```

## Properties

### An eventually constant sequence is asymptotically equal to the constant sequence of its eventual value

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  (H : is-eventually-constant-sequence u)
  where

  eventually-eq-constant-sequence :
    eventually-eq-sequence
      ( λ _ → value-eventually-constant-sequence u H)
      ( u)
  eventually-eq-constant-sequence =
    ( modulus-eventually-constant-sequence u H) ,
    ( λ n →
      is-modulus-modulus-eventually-constant-sequence u H
      ( modulus-eventually-constant-sequence u H)
      ( n)
      (refl-leq-ℕ (modulus-eventually-constant-sequence u H)))
```

### A constant sequence is eventually constant

```agda
module _
  {l : Level} {A : UU l} (x : A)
  where

  is-eventually-constant-const-sequence :
    is-eventually-constant-sequence (const ℕ x)
  is-eventually-constant-const-sequence = zero-ℕ , λ _ _ _ _ → refl
```

### A subsequence of an eventually constant sequence is eventually constant

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (v : subsequence u)
  where

  is-eventually-constant-subsequence :
    is-eventually-constant-sequence u →
    is-eventually-constant-sequence (sequence-subsequence u v)
  is-eventually-constant-subsequence =
    map-Σ
      ( is-modulus-eventually-constant-sequence (sequence-subsequence u v))
      ( modulus-is-unbounded-is-strictly-increasing-sequence-ℕ
        ( extract-subsequence u v)
        ( is-strictly-increasing-extract-subsequence u v))
      ( λ N K p q I J →
        K
          ( extract-subsequence u v p)
          ( extract-subsequence u v q)
          ( leq-bound-is-strictly-increasing-sequence-ℕ
            ( extract-subsequence u v)
            ( is-strictly-increasing-extract-subsequence u v)
            ( N)
            ( p)
            ( I))
          ( leq-bound-is-strictly-increasing-sequence-ℕ
            ( extract-subsequence u v)
            ( is-strictly-increasing-extract-subsequence u v)
            ( N)
            ( q)
            ( J)))
```

### A sequence is eventually constant if all its subsequences are eventually constant

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  ( eventually-constant-subsequences :
    (v : subsequence u) →
    is-eventually-constant-sequence (sequence-subsequence u v))
  where

  is-eventually-constant-is-eventually-constant-subsequence :
    is-eventually-constant-sequence u
  is-eventually-constant-is-eventually-constant-subsequence =
    eventually-constant-subsequences (refl-subsequence u)
```
