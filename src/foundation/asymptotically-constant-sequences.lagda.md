# Aymptotically constant Sequences

```agda
module foundation.asymptotically-constant-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.monotonic-endomaps-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.asymptotically-equal-sequences
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.sequences
open import foundation.subsequences
open import foundation.universe-levels
```

</details>

## Idea

A sequence `u` is **asymptotically constant** if `u p ＝ u q` for sufficiently
large `p` and `q`.

## Definition

### Asymptotically constant sequences

```agda
module _
  {l : Level} {A : UU l}
  where

  is-modulus-∞-constant-sequence : (u : sequence A) (N : ℕ) → UU l
  is-modulus-∞-constant-sequence u N =
    (p q : ℕ) → leq-ℕ N p → leq-ℕ N q → (u p) ＝ (u q)

  is-∞-constant-sequence : (u : sequence A) → UU l
  is-∞-constant-sequence u = Σ ℕ (is-modulus-∞-constant-sequence u)
```

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (H : is-∞-constant-sequence u)
  where

  modulus-∞-constant-sequence : ℕ
  modulus-∞-constant-sequence = pr1 H

  is-modulus-modulus-∞-constant-sequence :
    is-modulus-∞-constant-sequence u modulus-∞-constant-sequence
  is-modulus-modulus-∞-constant-sequence = pr2 H
```

## Properties

### The asymptotical value of an asymptotically constant sequence

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (H : is-∞-constant-sequence u)
  where

  ∞-value-∞-constant-sequence : A
  ∞-value-∞-constant-sequence = u (modulus-∞-constant-sequence u H)
```

### An asymptotically constant sequence is asymptotically equal to the constant sequence of its asymptotical value

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (H : is-∞-constant-sequence u)
  where

  eq-∞-constant-sequence :
    eq-∞-sequence (λ n → ∞-value-∞-constant-sequence u H) u
  eq-∞-constant-sequence =
    ( modulus-∞-constant-sequence u H) ,
    ( λ n →
      is-modulus-modulus-∞-constant-sequence u H
      ( modulus-∞-constant-sequence u H)
      ( n)
      (refl-leq-ℕ (modulus-∞-constant-sequence u H)))
```

### A subsequence of an asymptotically constant sequence is asymptotically constant

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (v : subsequence u)
  where

  is-∞-constant-subsequence :
    is-∞-constant-sequence u → is-∞-constant-sequence (sequence-subsequence u v)
  is-∞-constant-subsequence =
    map-Σ
      ( is-modulus-∞-constant-sequence (sequence-subsequence u v))
      ( modulus-limit-∞-is-strictly-increasing-endomap-ℕ
        ( extract-subsequence u v)
        ( is-strictly-increasing-extract-subsequence u v))
      ( λ N K p q I J →
        K
          ( extract-subsequence u v p)
          ( extract-subsequence u v q)
          ( is-modulus-modulus-limit-∞-is-strictly-increasing-endomap-ℕ
            ( extract-subsequence u v)
            ( is-strictly-increasing-extract-subsequence u v)
            ( N)
            ( p)
            ( I))
          ( is-modulus-modulus-limit-∞-is-strictly-increasing-endomap-ℕ
            ( extract-subsequence u v)
            ( is-strictly-increasing-extract-subsequence u v)
            ( N)
            ( q)
            ( J)))
```

### A sequence is asymptotically constant if all its subsequences are asymptotically constant

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  (H : (v : subsequence u) → is-∞-constant-sequence (sequence-subsequence u v))
  where

  is-∞-constant-is-∞-constant-subsequence : is-∞-constant-sequence u
  is-∞-constant-is-∞-constant-subsequence = H (refl-subsequence u)
```
