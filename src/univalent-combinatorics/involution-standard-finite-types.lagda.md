# An involution on the standard finite types

```agda
module univalent-combinatorics.involution-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.involutions
open import foundation.unit-type

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Every standard finite type `Fin k` has an involution operation given by
`x ↦ -x - 1`, using the group operations on `Fin k`.

## Definition

```agda
opposite-Fin : (k : ℕ) → Fin k → Fin k
opposite-Fin k x = pred-Fin k (neg-Fin k x)
```

## Properties

### The opposite function on `Fin k` is an involution

```agda
is-involution-opposite-Fin : (k : ℕ) → is-involution (opposite-Fin k)
is-involution-opposite-Fin k x =
  ( ap (pred-Fin k) (neg-pred-Fin k (neg-Fin k x))) ∙
  ( ( is-retraction-pred-Fin k (neg-Fin k (neg-Fin k x))) ∙
    ( neg-neg-Fin k x))

involution-opposite-Fin : (k : ℕ) → involution (Fin k)
involution-opposite-Fin k =
  opposite-Fin k ,
  is-involution-opposite-Fin k
```

### The opposite of `neg-one-Fin` is `zero-Fin`

```agda
abstract
  is-zero-opposite-neg-one-Fin :
    (n : ℕ) →
    is-zero-Fin (succ-ℕ n) (opposite-Fin (succ-ℕ n) (neg-one-Fin n))
  is-zero-opposite-neg-one-Fin n = equational-reasoning
    pred-Fin (succ-ℕ n) (neg-Fin (succ-ℕ n) (neg-one-Fin n))
    ＝
      add-Fin
        ( succ-ℕ n)
        ( neg-one-Fin n)
        ( neg-Fin (succ-ℕ n) (neg-one-Fin n))
      by is-add-neg-one-pred-Fin n (neg-Fin (succ-ℕ n) (neg-one-Fin n))
    ＝ zero-Fin n by right-inverse-law-add-Fin n (neg-one-Fin n)
```

### `nat-Fin-reverse` is the composition of `nat-Fin` with the involution operation

```agda
abstract
  opposite-nat-Fin-reverse :
    (n : ℕ) → (k : Fin n) → nat-Fin-reverse n k ＝ nat-Fin n (opposite-Fin n k)
  opposite-nat-Fin-reverse (succ-ℕ n) (inr star) =
    inv
      ( ap (nat-Fin (succ-ℕ n)) (is-zero-opposite-neg-one-Fin n) ∙
        is-zero-nat-zero-Fin {n})
  opposite-nat-Fin-reverse (succ-ℕ n) (inl k) = equational-reasoning
    succ-ℕ (nat-Fin-reverse n k)
    ＝ succ-ℕ (nat-Fin n (opposite-Fin n k))
      by ap succ-ℕ (opposite-nat-Fin-reverse n k)
    ＝ nat-Fin (succ-ℕ n) (opposite-Fin (succ-ℕ n) (inl k)) by {!   !}
```
