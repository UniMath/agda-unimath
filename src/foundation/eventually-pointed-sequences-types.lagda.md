# Eventually pointed sequences of types

```agda
module foundation.eventually-pointed-sequences-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-sequences
open import foundation.function-types
open import foundation.pi-decompositions
open import foundation.universe-levels
```

</details>

## Idea

A sequence of types `A : ℕ → UU l` is
{{# concept "eventually pointed" Disambiguation="sequence of types"}} if `A n`
is pointed for sufficiently
[large](elementary-number-theory.inequality-natural-numbers.md)
[natural numbers](elementary-number-theory.natural-numbers.md) `n`.

## Definitions

### Eventually pointed sequences of types

```agda
module _
  {l : Level} (A : ℕ → UU l)
  where

  is-modulus-eventually-pointed-sequence : ℕ → UU l
  is-modulus-eventually-pointed-sequence N = (n : ℕ) → leq-ℕ N n → A n

  has-modulus-eventually-pointed-sequence : UU l
  has-modulus-eventually-pointed-sequence =
    Σ ℕ is-modulus-eventually-pointed-sequence
```

### Modulus of an eventually pointed sequence of types

```agda
module _
  {l : Level} {A : ℕ → UU l} (H : has-modulus-eventually-pointed-sequence A)
  where

  modulus-has-modulus-eventually-pointed-sequence : ℕ
  modulus-has-modulus-eventually-pointed-sequence = pr1 H

  is-modulus-modulus-has-modulus-eventually-pointed-sequence :
    is-modulus-eventually-pointed-sequence A
      modulus-has-modulus-eventually-pointed-sequence
  is-modulus-modulus-has-modulus-eventually-pointed-sequence = pr2 H

  value-at-modulus-has-modulus-eventually-pointed-sequence :
    A modulus-has-modulus-eventually-pointed-sequence
  value-at-modulus-has-modulus-eventually-pointed-sequence =
    is-modulus-modulus-has-modulus-eventually-pointed-sequence
      ( modulus-has-modulus-eventually-pointed-sequence)
      ( refl-leq-ℕ modulus-has-modulus-eventually-pointed-sequence)
```

## Properties

### Pointed sequences are eventually pointed

```agda
module _
  {l : Level} {A : ℕ → UU l}
  where

  has-modulus-eventually-pointed-Π :
    Π ℕ A → has-modulus-eventually-pointed-sequence A
  has-modulus-eventually-pointed-Π u = zero-ℕ , λ p _ → u p
```

### Any natural number greater than an eventual modulus is an eventual modulus

```agda
module _
  {l : Level} (A : ℕ → UU l) (i j : ℕ) (I : leq-ℕ i j)
  where

  is-modulus-leq-modulus-has-modulus-eventually-pointed-seqence :
    is-modulus-eventually-pointed-sequence A i →
    is-modulus-eventually-pointed-sequence A j
  is-modulus-leq-modulus-has-modulus-eventually-pointed-seqence H k K =
    H k (transitive-leq-ℕ i j k K I)
```

### A sequence that eventually is eventually pointed is eventually pointed

```agda
module _
  {l : Level} (A : ℕ → UU l)
  where

  has-modulus-eventually-pointed-is-eventually-modulus-eventually-pointed-sequence :
    has-modulus-eventually-pointed-sequence
      (is-modulus-eventually-pointed-sequence A) →
    has-modulus-eventually-pointed-sequence A
  has-modulus-eventually-pointed-is-eventually-modulus-eventually-pointed-sequence
    (N , H) = N , λ n K → H n K n (refl-leq-ℕ n)
```

### Eventual functorial action on eventually pointed sequences

```agda
module _
  {l1 l2 : Level} {A : ℕ → UU l1} {B : ℕ → UU l2}
  where

  map-has-modulus-eventually-pointed-sequence :
    has-modulus-eventually-pointed-sequence (λ n → A n → B n) →
    has-modulus-eventually-pointed-sequence A →
    has-modulus-eventually-pointed-sequence B
  map-has-modulus-eventually-pointed-sequence H K =
    ( max-ℕ
      ( modulus-has-modulus-eventually-pointed-sequence H)
      ( modulus-has-modulus-eventually-pointed-sequence K)) ,
    ( λ m I →
      is-modulus-modulus-has-modulus-eventually-pointed-sequence H m
        ( leq-left-leq-max-ℕ m
          ( modulus-has-modulus-eventually-pointed-sequence H)
          ( modulus-has-modulus-eventually-pointed-sequence K)
          ( I))
        ( is-modulus-modulus-has-modulus-eventually-pointed-sequence K m
          ( leq-right-leq-max-ℕ m
            ( modulus-has-modulus-eventually-pointed-sequence H)
            ( modulus-has-modulus-eventually-pointed-sequence K)
            ( I))))

  map-Π-has-modulus-eventually-pointed-sequence :
    ((n : ℕ) → A n → B n) →
    has-modulus-eventually-pointed-sequence A →
    has-modulus-eventually-pointed-sequence B
  map-Π-has-modulus-eventually-pointed-sequence =
    map-has-modulus-eventually-pointed-sequence ∘
    has-modulus-eventually-pointed-Π
```

### Eventual binary functorial action on eventually pointed sequences

```agda
module _
  {l1 l2 l3 : Level} {A : ℕ → UU l1} {B : ℕ → UU l2} {C : ℕ → UU l3}
  where

  map-binary-has-modulus-eventually-pointed-sequence :
    has-modulus-eventually-pointed-sequence (λ n → A n → B n → C n) →
    has-modulus-eventually-pointed-sequence A →
    has-modulus-eventually-pointed-sequence B →
    has-modulus-eventually-pointed-sequence C
  map-binary-has-modulus-eventually-pointed-sequence I =
    map-has-modulus-eventually-pointed-sequence ∘
    map-has-modulus-eventually-pointed-sequence I

  map-binary-Π-has-modulus-eventually-pointed-sequence :
    ((n : ℕ) → A n → B n → C n) →
    has-modulus-eventually-pointed-sequence A →
    has-modulus-eventually-pointed-sequence B →
    has-modulus-eventually-pointed-sequence C
  map-binary-Π-has-modulus-eventually-pointed-sequence =
    map-binary-has-modulus-eventually-pointed-sequence ∘
    has-modulus-eventually-pointed-Π
```
