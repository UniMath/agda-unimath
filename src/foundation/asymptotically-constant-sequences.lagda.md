# Asymptotically constant sequences

```agda
module foundation.asymptotically-constant-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.monotonic-sequences-natural-numbers
open import elementary-number-theory.natural-numbers

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

A sequence `u` is **asymptotically constant** if `u p ＝ u q` for sufficiently
large `p` and `q`.

## Definition

### Asymptotically constant sequences

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  is-∞-constant-sequence : UU l
  is-∞-constant-sequence =
    asymptotically (λ p → asymptotically (λ q → u p ＝ u q))
```

### The asymptotical value of an asymptotically constant sequence

```agda
module _
  {l : Level} {A : UU l} {u : sequence A} (H : is-∞-constant-sequence u)
  where

  ∞-value-∞-constant-sequence : A
  ∞-value-∞-constant-sequence = u (modulus-∞-asymptotically H)

  modulus-∞-value-∞-constant-sequence : ℕ
  modulus-∞-value-∞-constant-sequence =
    modulus-∞-asymptotically (value-∞-asymptotically H)

  is-modulus-∞-value-∞-constant-sequence :
    (n : ℕ) →
    leq-ℕ modulus-∞-value-∞-constant-sequence n →
    ∞-value-∞-constant-sequence ＝ u n
  is-modulus-∞-value-∞-constant-sequence =
    is-modulus-∞-asymptotically (value-∞-asymptotically H)
```

## Properties

### Constant sequences are asymptotically constant

```agda
module _
  {l : Level} {A : UU l} {u : sequence A} (H : is-constant-sequence u)
  where

  is-∞-constant-is-constant-sequence : is-∞-constant-sequence u
  pr1 is-∞-constant-is-constant-sequence = zero-ℕ
  pr2 is-∞-constant-is-constant-sequence p I = (zero-ℕ , λ q J → H p q)
```

### The asymptotical value of an asymptotically constant sequence is unique

```agda
module _
  {l : Level} {A : UU l} {u : sequence A}
  (H K : is-∞-constant-sequence u)
  where

  all-equal-∞-value-∞-constant-sequence :
    ∞-value-∞-constant-sequence H ＝ ∞-value-∞-constant-sequence K
  all-equal-∞-value-∞-constant-sequence =
    ( is-modulus-∞-value-∞-constant-sequence
      ( H)
      ( max-ℕ
        ( modulus-∞-value-∞-constant-sequence H)
        ( modulus-∞-value-∞-constant-sequence K))
      ( leq-left-leq-max-ℕ
        ( max-ℕ
          ( modulus-∞-value-∞-constant-sequence H)
          ( modulus-∞-value-∞-constant-sequence K))
        ( modulus-∞-value-∞-constant-sequence H)
        ( modulus-∞-value-∞-constant-sequence K)
        ( refl-leq-ℕ
          ( max-ℕ
            ( modulus-∞-value-∞-constant-sequence H)
            ( modulus-∞-value-∞-constant-sequence K))))) ∙
    ( inv
      ( is-modulus-∞-value-∞-constant-sequence
        ( K)
        ( max-ℕ
          ( modulus-∞-value-∞-constant-sequence H)
          ( modulus-∞-value-∞-constant-sequence K))
        ( leq-right-leq-max-ℕ
          ( max-ℕ
            ( modulus-∞-value-∞-constant-sequence H)
            ( modulus-∞-value-∞-constant-sequence K))
          ( modulus-∞-value-∞-constant-sequence H)
          ( modulus-∞-value-∞-constant-sequence K)
          ( refl-leq-ℕ
            ( max-ℕ
              ( modulus-∞-value-∞-constant-sequence H)
              ( modulus-∞-value-∞-constant-sequence K))))))
```

### An asymptotically constant sequence is asymptotically equal to the constant sequence of its asymptotical value

```agda
module _
  {l : Level} {A : UU l} {u : sequence A} (H : is-∞-constant-sequence u)
  where

  eq-∞-value-∞-constant-sequence :
    eq-∞-sequence (const-sequence (∞-value-∞-constant-sequence H)) u
  eq-∞-value-∞-constant-sequence =
    ( modulus-∞-value-∞-constant-sequence H) ,
    ( is-modulus-∞-value-∞-constant-sequence H)
```

### A sequence is asymptotically constant if it is asymptotically equal to some constant sequence

```agda
module _
  {l : Level} {A : UU l} (x : A) (u : sequence A)
  where

  is-∞-constant-eq-∞-constant-sequence :
    (eq-∞-sequence (const-sequence x) u) → is-∞-constant-sequence u
  is-∞-constant-eq-∞-constant-sequence H =
    ( modulus-eq-∞-sequence H) ,
    ( λ p I →
      ( ( modulus-eq-∞-sequence H) ,
        ( λ q J →
          ( inv
            ( is-modulus-eq-∞-sequence H p I)) ∙
          ( is-modulus-eq-∞-sequence H q J))))
```

### Any subsequence of an asymptotically constant sequence is asymptotically constant

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (v : subsequence u)
  where

  eq-∞-value-∞-constant-subsequence :
    (H : is-∞-constant-sequence u) →
    eq-∞-sequence
      ( const-sequence (∞-value-∞-constant-sequence H))
      ( sequence-subsequence u v)
  eq-∞-value-∞-constant-subsequence H =
    ( ( modulus-subsequence u v (modulus-∞-value-∞-constant-sequence H)) ,
      ( λ n I →
        is-modulus-∞-value-∞-constant-sequence H
          ( extract-subsequence u v n)
          ( is-modulus-subsequence u v
            ( modulus-∞-value-∞-constant-sequence H)
            ( n)
            ( I))))

  is-∞-constant-subsequence :
    is-∞-constant-sequence u → is-∞-constant-sequence (sequence-subsequence u v)
  is-∞-constant-subsequence H =
    is-∞-constant-eq-∞-constant-sequence
      ( ∞-value-∞-constant-sequence H)
      ( sequence-subsequence u v)
      ( eq-∞-value-∞-constant-subsequence H)
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

### A sequence asymptotically equal to an asymptotically constant sequence is asymptotically constant

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A) (H : eq-∞-sequence u v)
  where

  preserves-∞-constant-eq-∞-sequence :
    is-∞-constant-sequence u → is-∞-constant-sequence v
  preserves-∞-constant-eq-∞-sequence K =
    is-∞-constant-eq-∞-constant-sequence
      ( ∞-value-∞-constant-sequence K)
      ( v)
      ( transitive-eq-∞-sequence
        ( const-sequence (∞-value-∞-constant-sequence K))
        ( u)
        ( v)
        ( H)
        ( eq-∞-value-∞-constant-sequence K))
```

### Asymptotically stationnary sequences

#### The type of being asymptotically stationnary

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  is-∞-stationnary-sequence : UU l
  is-∞-stationnary-sequence = asymptotically (λ n → u n ＝ u (succ-ℕ n))

  is-∞-constant-modulus-is-∞-stationnary-sequence :
    (H : is-∞-stationnary-sequence) →
    (n : ℕ) →
    leq-ℕ (modulus-∞-asymptotically H) n →
    u (modulus-∞-asymptotically H) ＝ u n
  is-∞-constant-modulus-is-∞-stationnary-sequence H =
    based-ind-ℕ
      ( modulus-∞-asymptotically H)
      ( λ n → u (modulus-∞-asymptotically H) ＝ u n)
      ( refl)
      ( λ n I K → K ∙ is-modulus-∞-asymptotically H n I)
```

#### A sequence is asymptotically constant if and only if it is asymptotically stationnary

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  is-∞-constant-is-∞-stationnary :
    is-∞-stationnary-sequence u → is-∞-constant-sequence u
  is-∞-constant-is-∞-stationnary H =
    is-∞-constant-eq-∞-constant-sequence
      ( u (modulus-∞-asymptotically H))
      ( u)
      ( ( modulus-∞-asymptotically H) ,
        ( is-∞-constant-modulus-is-∞-stationnary-sequence u H))

  is-∞-stationnary-is-∞-constant-sequence :
    is-∞-constant-sequence u → is-∞-stationnary-sequence u
  is-∞-stationnary-is-∞-constant-sequence H =
    ( ( modulus-∞-value-∞-constant-sequence H) ,
      ( λ n I →
        ( inv (is-modulus-∞-value-∞-constant-sequence H n I)) ∙
        ( is-modulus-∞-value-∞-constant-sequence
          ( H)
          ( succ-ℕ n)
          ( preserves-leq-succ-ℕ
            ( modulus-∞-value-∞-constant-sequence H)
            ( n)
            ( I)))))
```

### A sequence is asymptotically constant if and only if it is asymptotically equal to all its subsequences

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  eq-∞-subsequence-is-∞-constant-sequence :
    is-∞-constant-sequence u →
    ((v : subsequence u) → eq-∞-sequence u (sequence-subsequence u v))
  eq-∞-subsequence-is-∞-constant-sequence H v =
    transitive-eq-∞-sequence
      ( u)
      ( const-sequence (∞-value-∞-constant-sequence H))
      ( sequence-subsequence u v)
      ( eq-∞-value-∞-constant-subsequence u v H)
      ( symmetric-eq-∞-sequence
        ( const-sequence (∞-value-∞-constant-sequence H))
        ( u)
        ( eq-∞-value-∞-constant-sequence H))

  is-∞-constant-eq-∞-sequence-subsequence :
    ((v : subsequence u) → eq-∞-sequence u (sequence-subsequence u v)) →
    is-∞-constant-sequence u
  is-∞-constant-eq-∞-sequence-subsequence H =
    is-∞-constant-is-∞-stationnary
      ( u)
      ( H (skip-zero-sequence u))
```
