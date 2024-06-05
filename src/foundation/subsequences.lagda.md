# Subsequences

```agda
module foundation.subsequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strict-monotonic-sequences-natural-numbers

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
[strictly increasing](elementary-number-theory.strict-monotonic-sequences-natural-numbers.md)
map `f : ℕ → ℕ`.

## Definitions

### Subsequences

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  subsequence : UU lzero
  subsequence = strict-increasing-sequence-ℕ
```

### The extracted sequence of a subsequence

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (v : subsequence u)
  where

  extract-subsequence : ℕ → ℕ
  extract-subsequence =
    sequence-strict-increasing-sequence-ℕ v

  is-strict-increasing-extract-subsequence :
    is-strict-increasing-sequence-ℕ extract-subsequence
  is-strict-increasing-extract-subsequence =
    is-strict-increasing-sequence-strict-increasing-sequence-ℕ v

  leq-id-extract-subsequence :
    (p : ℕ) → leq-ℕ p (extract-subsequence p)
  leq-id-extract-subsequence = leq-id-strict-increasing-sequence-ℕ v

  preserves-leq-extract-subsequence :
    (p q : ℕ) →
    leq-ℕ p q →
    leq-ℕ (extract-subsequence p) (extract-subsequence q)
  preserves-leq-extract-subsequence =
    preserves-leq-strict-increasing-sequence-ℕ v

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
  refl-subsequence = strict-increasing-id-ℕ

  compute-refl-subsequence : u ＝ sequence-subsequence u refl-subsequence
  compute-refl-subsequence = refl
```

### The subsequence that skips the first term

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  skip-zero-sequence : subsequence u
  skip-zero-sequence = strict-increasing-succ-ℕ

  compute-skip-zero-sequence :
    u ∘ succ-ℕ ＝ sequence-subsequence u skip-zero-sequence
  compute-skip-zero-sequence = refl
```

### The subsequence that skips the `n + 1` first terms

```agda
module _
  {l : Level} {A : UU l} (n : ℕ) (u : sequence A)
  where

  skip-subsequence : subsequence u
  skip-subsequence = strict-increasing-skip-ℕ n

  compute-skip-subsequence :
    u ∘ (succ-ℕ ∘ add-ℕ n) ＝ sequence-subsequence u skip-subsequence
  compute-skip-subsequence = refl
```

### A subsequence of a subsequence is a subsequence of the original sequence

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (v : subsequence u)
  (w : subsequence (sequence-subsequence u v))
  where

  sub-subsequence : subsequence u
  sub-subsequence = comp-strict-increasing-sequence-ℕ v w

  compute-sub-subsequence :
    Id
      (sequence-subsequence u sub-subsequence)
      (sequence-subsequence (sequence-subsequence u v) w)
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
    modulus-limit-∞-is-strict-increasing-sequence-ℕ
      ( extract-subsequence u v)
      ( is-strict-increasing-extract-subsequence u v)

  is-modulus-subsequence :
    (N p : ℕ) →
    leq-ℕ (modulus-subsequence N) p →
    leq-ℕ N (extract-subsequence u v p)
  is-modulus-subsequence =
    is-modulus-limit-∞-is-strict-increasing-sequence-ℕ
      ( extract-subsequence u v)
      ( is-strict-increasing-extract-subsequence u v)

  extract-modulus-subsequence : ℕ → ℕ
  extract-modulus-subsequence = extract-subsequence u v ∘ modulus-subsequence

  leq-extract-modulus-subsequence :
    (n : ℕ) → leq-ℕ n (extract-modulus-subsequence n)
  leq-extract-modulus-subsequence n =
    is-modulus-subsequence
      ( n)
      ( modulus-subsequence n)
      ( refl-leq-ℕ (modulus-subsequence n))
```

### Subsequential type families

```agda
module _
  {l l1 : Level} {A : UU l} (P : sequence A → UU l1)
  where

  Π-subsequence : sequence A → UU l1
  Π-subsequence u = (v : subsequence u) → P (sequence-subsequence u v)

  sequence-Π-subsequence : (u : sequence A) → Π-subsequence u → P u
  sequence-Π-subsequence u H = H (refl-subsequence u)

  Σ-subsequence : sequence A → UU l1
  Σ-subsequence u = Σ (subsequence u) (P ∘ (sequence-subsequence u))

  sequence-Σ-subsequence : (u : sequence A) → P u → Σ-subsequence u
  sequence-Σ-subsequence u H = (refl-subsequence u , H)
```

### A dependent sequence is asymptotical if and only if all its subsequences are asymptotical

```agda
module _
  {l : Level} (A : ℕ → UU l) (H : asymptotically A)
  where

  asymptotically-Π-subsequence : Π-subsequence asymptotically A
  asymptotically-Π-subsequence B =
    map-Σ
      ( is-modulus-dependent-sequence (sequence-subsequence A B))
      ( modulus-subsequence A B)
      ( λ N K p →
        ( K (extract-subsequence A B p)) ∘
        ( is-modulus-subsequence A B N p))
      ( H)
```
