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
{{# concept "eventually pointed" Disambiguation="sequence of types"}}
if `A n` is pointed for sufficiently
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

  is-eventually-pointed-sequence : UU l
  is-eventually-pointed-sequence = Σ ℕ is-modulus-eventually-pointed-sequence
```

### Modulus of an eventually pointed sequence of types

```agda
module _
  {l : Level} {A : ℕ → UU l} (H : is-eventually-pointed-sequence A)
  where

  modulus-is-eventually-pointed-sequence : ℕ
  modulus-is-eventually-pointed-sequence = pr1 H

  is-modulus-modulus-is-eventually-pointed-sequence :
    is-modulus-eventually-pointed-sequence A
      modulus-is-eventually-pointed-sequence
  is-modulus-modulus-is-eventually-pointed-sequence = pr2 H

  value-is-eventually-pointed-sequence :
    A modulus-is-eventually-pointed-sequence
  value-is-eventually-pointed-sequence =
    is-modulus-modulus-is-eventually-pointed-sequence
      ( modulus-is-eventually-pointed-sequence)
      ( refl-leq-ℕ modulus-is-eventually-pointed-sequence)
```

## Properties

### Pointed sequences are eventually pointed

```agda
module _
  {l : Level} {A : ℕ → UU l}
  where

  is-eventually-pointed-Π : Π ℕ A → is-eventually-pointed-sequence A
  is-eventually-pointed-Π u = zero-ℕ , λ p _ → u p
```

### Any natural number greater than an eventual modulus is an eventual modulus

```agda
module _
  {l : Level} (A : ℕ → UU l) (i j : ℕ) (I : leq-ℕ i j)
  where

  is-modulus-leq-modulus-is-eventually-pointed-seqence :
    is-modulus-eventually-pointed-sequence A i →
    is-modulus-eventually-pointed-sequence A j
  is-modulus-leq-modulus-is-eventually-pointed-seqence H k K =
    H k (transitive-leq-ℕ i j k K I)
```

### A sequence that eventually is eventually pointed is eventually pointed

```agda
module _
  {l : Level} (A : ℕ → UU l)
  where

  is-eventually-pointed-is-eventually-modulus-eventually-pointed-sequence :
    is-eventually-pointed-sequence (is-modulus-eventually-pointed-sequence A) →
    is-eventually-pointed-sequence A
  is-eventually-pointed-is-eventually-modulus-eventually-pointed-sequence
    (N , H) = N , λ n K → H n K n (refl-leq-ℕ n)
```

### Eventual functorial action on eventually pointed sequences

```agda
module _
  {l1 l2 : Level} {A : ℕ → UU l1} {B : ℕ → UU l2}
  where

  map-is-eventually-pointed-sequence :
    is-eventually-pointed-sequence (λ n → A n → B n) →
    is-eventually-pointed-sequence A →
    is-eventually-pointed-sequence B
  map-is-eventually-pointed-sequence H K =
    ( max-ℕ
      ( modulus-is-eventually-pointed-sequence H)
      ( modulus-is-eventually-pointed-sequence K)) ,
    ( λ m I →
      is-modulus-modulus-is-eventually-pointed-sequence H m
        ( leq-left-leq-max-ℕ m
          ( modulus-is-eventually-pointed-sequence H)
          ( modulus-is-eventually-pointed-sequence K)
          ( I))
        ( is-modulus-modulus-is-eventually-pointed-sequence K m
          ( leq-right-leq-max-ℕ m
            ( modulus-is-eventually-pointed-sequence H)
            ( modulus-is-eventually-pointed-sequence K)
            ( I))))

  map-Π-is-eventually-pointed-sequence :
    ((n : ℕ) → A n → B n) →
    is-eventually-pointed-sequence A →
    is-eventually-pointed-sequence B
  map-Π-is-eventually-pointed-sequence =
    map-is-eventually-pointed-sequence ∘ is-eventually-pointed-Π
```

### Eventual binary functorial action on eventually pointed sequences

```agda
module _
  {l1 l2 l3 : Level} {A : ℕ → UU l1} {B : ℕ → UU l2} {C : ℕ → UU l3}
  where

  map-binary-is-eventually-pointed-sequence :
    is-eventually-pointed-sequence (λ n → A n → B n → C n) →
    is-eventually-pointed-sequence A →
    is-eventually-pointed-sequence B →
    is-eventually-pointed-sequence C
  map-binary-is-eventually-pointed-sequence I =
    map-is-eventually-pointed-sequence ∘
    map-is-eventually-pointed-sequence I

  map-binary-Π-is-eventually-pointed-sequence :
    ((n : ℕ) → A n → B n → C n) →
    is-eventually-pointed-sequence A →
    is-eventually-pointed-sequence B →
    is-eventually-pointed-sequence C
  map-binary-Π-is-eventually-pointed-sequence =
    map-binary-is-eventually-pointed-sequence ∘ is-eventually-pointed-Π
```
