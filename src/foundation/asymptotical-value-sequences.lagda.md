# Asymptotical value of a sequence

```agda
module foundation.asymptotical-value-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strictly-increasing-sequences-natural-numbers

open import foundation.asymptotical-dependent-sequences
open import foundation.asymptotically-equal-sequences
open import foundation.constant-sequences
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.sequences
open import foundation.subsequences
open import foundation.universe-levels
```

</details>

## Idea

A sequence `u` in a type `A` has an **asymptotical value** `x : A` if `x ＝ u n`
for sufficiently large natural numbers `n`.

## Definitions

### Asymptotical values of sequences

```agda
module _
  {l : Level} {A : UU l} (x : A) (u : sequence A)
  where

  is-∞-value-sequence : UU l
  is-∞-value-sequence = asymptotically (is-value-sequence x u)
```

### Modulus of an asymptotical value of a sequence

```agda
module _
  {l : Level} {A : UU l} {x : A} {u : sequence A} (H : is-∞-value-sequence x u)
  where

  modulus-∞-value-sequence : ℕ
  modulus-∞-value-sequence = pr1 H

  is-modulus-∞-value-sequence :
    (n : ℕ) → leq-ℕ modulus-∞-value-sequence n → x ＝ u n
  is-modulus-∞-value-sequence = pr2 H
```

## Properties

### Asymptotical values are unique

```agda
module _
  {l : Level} {A : UU l} (x y : A) (u : sequence A)
  (H : is-∞-value-sequence x u) (K : is-∞-value-sequence y u)
  where

  all-eq-∞-value-sequence : x ＝ y
  all-eq-∞-value-sequence =
    value-∞-asymptotically
      (map-binary-asymptotically-Π (λ n I J → I ∙ (inv J)) H K)
```

### A sequence has an asymptotical value if and only if it is asymptotically equal to some constant sequence

```agda
module _
  {l : Level} {A : UU l} (x : A) (u : sequence A)
  where

  eq-∞-const-sequence-is-∞-value-sequence :
    is-∞-value-sequence x u → eq-∞-sequence (const-sequence x) u
  eq-∞-const-sequence-is-∞-value-sequence = tot (λ n K → K)

  is-∞-value-eq-∞-constant-sequence :
    eq-∞-sequence (const-sequence x) u → is-∞-value-sequence x u
  is-∞-value-eq-∞-constant-sequence = tot (λ n K → K)
```

### Asymptotical equality preserves asymptotical value

```agda
module _
  {l : Level} {A : UU l} (x : A) (u v : sequence A)
  where

  preserves-∞-value-eq-∞-sequence :
    eq-∞-sequence u v → is-∞-value-sequence x u → is-∞-value-sequence x v
  preserves-∞-value-eq-∞-sequence =
    map-binary-asymptotically-Π (λ n I H → H ∙ I)
```

### The asymptotical value of a sequence is an asymptotical value of all it subsequences

```agda
module _
  {l : Level} {A : UU l} {x : A} {u : sequence A} (H : is-∞-value-sequence x u)
  where

  Π-subsequence-∞-value-sequence : Π-subsequence (is-∞-value-sequence x) u
  Π-subsequence-∞-value-sequence v =
    ( modulus-subsequence u v (modulus-∞-value-sequence H)) ,
    ( λ n I →
      is-modulus-∞-value-sequence
        ( H)
        ( extract-subsequence u v n)
        ( is-modulus-subsequence u v (modulus-∞-value-sequence H) n I))
```
