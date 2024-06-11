# Asymptotically constant sequences

```agda
module foundation.asymptotically-constant-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strictly-increasing-sequences-natural-numbers

open import foundation.asymptotical-dependent-sequences
open import foundation.asymptotical-value-sequences
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

## Definitions

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

  is-∞-value-∞-constant-sequence :
    is-∞-value-sequence ∞-value-∞-constant-sequence u
  is-∞-value-∞-constant-sequence = value-∞-asymptotically H

  modulus-∞-value-∞-constant-sequence : ℕ
  modulus-∞-value-∞-constant-sequence =
    modulus-∞-asymptotically is-∞-value-∞-constant-sequence

  is-modulus-∞-value-∞-constant-sequence :
    (n : ℕ) →
    leq-ℕ modulus-∞-value-∞-constant-sequence n →
    ∞-value-∞-constant-sequence ＝ u n
  is-modulus-∞-value-∞-constant-sequence =
    is-modulus-∞-asymptotically is-∞-value-∞-constant-sequence

  const-∞-value-∞-constant-sequence : sequence A
  const-∞-value-∞-constant-sequence n = ∞-value-∞-constant-sequence
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
    all-eq-∞-value-sequence
      ( ∞-value-∞-constant-sequence H)
      ( ∞-value-∞-constant-sequence K)
      ( u)
      ( is-∞-value-∞-constant-sequence H)
      ( is-∞-value-∞-constant-sequence K)
```

### A sequence is asymptotically constant if it has some asymptotical value

```agda
module _
  {l : Level} {A : UU l} (x : A) (u : sequence A)
  where

  ∞-constant-is-∞-value-sequence :
    is-∞-value-sequence x u → is-∞-constant-sequence u
  ∞-constant-is-∞-value-sequence H =
    ( modulus-∞-value-sequence H) ,
    ( λ p I →
      ( modulus-∞-value-sequence H) ,
      ( λ q J →
        ( inv (is-modulus-∞-value-sequence H p I)) ∙
        ( is-modulus-∞-value-sequence H q J)))
```

### An asymptotically constant sequence is asymptotically equal to the constant sequence of its asymptotical value

```agda
module _
  {l : Level} {A : UU l} {u : sequence A} (H : is-∞-constant-sequence u)
  where

  eq-∞-value-∞-constant-sequence :
    eq-∞-sequence (const-∞-value-∞-constant-sequence H) u
  eq-∞-value-∞-constant-sequence =
    ( modulus-∞-value-∞-constant-sequence H) ,
    ( is-modulus-∞-value-∞-constant-sequence H)

  eq-∞-value-∞-constant-sequence' :
    eq-∞-sequence u (const-∞-value-∞-constant-sequence H)
  eq-∞-value-∞-constant-sequence' =
    inv-eq-∞-sequence eq-∞-value-∞-constant-sequence
```

### Two asymptotically constant sequences are asymptotically equal if and only if their asymptotical value is the same

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A)
  (H : is-∞-constant-sequence u) (K : is-∞-constant-sequence v)
  where

  eq-∞-sequence-eq-∞-value-∞-constant-sequence :
    (∞-value-∞-constant-sequence H) ＝ (∞-value-∞-constant-sequence K) →
    eq-∞-sequence u v
  eq-∞-sequence-eq-∞-value-∞-constant-sequence I =
    conjugate-eq-∞-sequence
      ( eq-∞-value-∞-constant-sequence H)
      ( eq-∞-value-∞-constant-sequence K)
      ( asymptotically-Π (λ n → I))

  eq-∞-value-eq-∞-sequence-∞-constant-sequence :
    eq-∞-sequence u v →
    (∞-value-∞-constant-sequence H) ＝ (∞-value-∞-constant-sequence K)
  eq-∞-value-eq-∞-sequence-∞-constant-sequence I =
    value-∞-asymptotically
    ( conjugate-eq-∞-sequence'
      ( eq-∞-value-∞-constant-sequence H)
      ( eq-∞-value-∞-constant-sequence K)
      ( I))
```

### Any subsequence of an asymptotically constant sequence is asymptotically constant

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (H : is-∞-constant-sequence u)
  where

  ∞-constant-Π-subsequence : Π-subsequence is-∞-constant-sequence u
  ∞-constant-Π-subsequence v =
    ∞-constant-is-∞-value-sequence
      ( ∞-value-∞-constant-sequence H)
      ( sequence-subsequence u v)
      ( Π-subsequence-∞-value-sequence
        ( is-∞-value-∞-constant-sequence H)
        ( v))
```

### A sequence asymptotically equal to an asymptotically constant sequence is asymptotically constant

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A) (H : eq-∞-sequence u v)
  where

  preserves-∞-constant-eq-∞-sequence :
    is-∞-constant-sequence u → is-∞-constant-sequence v
  preserves-∞-constant-eq-∞-sequence K =
    ∞-constant-is-∞-value-sequence
      ( ∞-value-∞-constant-sequence K)
      ( v)
      ( transitive-eq-∞-sequence
        ( const-∞-value-∞-constant-sequence K)
        ( u)
        ( v)
        ( H)
        ( eq-∞-value-∞-constant-sequence K))
```

### Asymptotically stationnary sequences

#### The predicate of being asymptotically stationnary

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  is-∞-stationnary-sequence : UU l
  is-∞-stationnary-sequence = asymptotically (is-stationnary-value-sequence u)

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

  ∞-constant-is-∞-stationnary-sequence :
    is-∞-stationnary-sequence u → is-∞-constant-sequence u
  ∞-constant-is-∞-stationnary-sequence H =
    ∞-constant-is-∞-value-sequence
      ( u (modulus-∞-asymptotically H))
      ( u)
      ( ( modulus-∞-asymptotically H) ,
        ( is-∞-constant-modulus-is-∞-stationnary-sequence u H))

  ∞-stationnary-is-∞-constant-sequence :
    is-∞-constant-sequence u → is-∞-stationnary-sequence u
  ∞-stationnary-is-∞-constant-sequence H =
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
    is-∞-constant-sequence u → Π-subsequence (eq-∞-sequence u) u
  eq-∞-subsequence-is-∞-constant-sequence H v =
    transitive-eq-∞-sequence
      ( u)
      ( const-∞-value-∞-constant-sequence H)
      ( sequence-subsequence u v)
      ( eq-∞-const-sequence-is-∞-value-sequence
        ( ∞-value-∞-constant-sequence H)
        ( sequence-subsequence u v)
        ( Π-subsequence-∞-value-sequence (is-∞-value-∞-constant-sequence H) v))
      ( eq-∞-value-∞-constant-sequence' H)

  ∞-constant-eq-∞-sequence-subsequence :
    Π-subsequence (eq-∞-sequence u) u → is-∞-constant-sequence u
  ∞-constant-eq-∞-sequence-subsequence H =
    ∞-constant-is-∞-stationnary-sequence
      ( u)
      ( H (skip-zero-sequence u))
```

### An asymptotically constant sequence has a constant subsequence

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (H : is-∞-constant-sequence u)
  where

  constant-subsequence-is-∞-constant-sequence :
    Σ-subsequence is-constant-sequence u
  constant-subsequence-is-∞-constant-sequence =
    ( skip-subsequence (modulus-∞-value-∞-constant-sequence H) u) ,
    ( λ p q →
      ( inv
        ( is-modulus-∞-value-∞-constant-sequence
          ( H)
          ( skip-ℕ (modulus-∞-value-∞-constant-sequence H) p)
          ( leq-add-ℕ (modulus-∞-value-∞-constant-sequence H) (succ-ℕ p)))) ∙
      ( is-modulus-∞-value-∞-constant-sequence
        ( H)
        ( skip-ℕ (modulus-∞-value-∞-constant-sequence H) q)
        ( leq-add-ℕ (modulus-∞-value-∞-constant-sequence H) (succ-ℕ q))))
```
