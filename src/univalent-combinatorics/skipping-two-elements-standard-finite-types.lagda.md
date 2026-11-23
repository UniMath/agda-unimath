# Skipping two elements in standard finite types

```agda
module univalent-combinatorics.skipping-two-elements-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.unit-type

open import univalent-combinatorics.skipping-element-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `n` and
two [distinct](foundation.negated-equality.md) elements `i` and `j` of
`Fin (n + 2)`, we can map any element of `Fin n` to a unique element of
`Fin (n + 2)` equal to neither `i` nor `j`.

## Definition

```agda
skip-two-Fin :
  (n : ℕ) (i j : Fin (n +ℕ 2)) → i ≠ j → Fin n → Fin (n +ℕ 2)
skip-two-Fin (succ-ℕ n) (inl i) (inl j) i≠j (inl k) =
  inl (skip-two-Fin n i j (nonequal-map inl i≠j) k)
skip-two-Fin (succ-ℕ n) (inl i) (inl j) i≠j (inr star) =
  inr star
skip-two-Fin (succ-ℕ n) (inl i) (inr star) i≠j k =
  inl (skip-Fin (succ-ℕ n) i k)
skip-two-Fin (succ-ℕ n) (inr star) (inl j) i≠j k =
  inl (skip-Fin (succ-ℕ n) j k)
skip-two-Fin (succ-ℕ n) (inr star) (inr star) i≠j k =
  ex-falso (i≠j refl)
```

## Properties

### `skip-two-Fin` in terms of `skip-Fin`

```agda
skip-two-Fin' :
  (n : ℕ) (i j : Fin (n +ℕ 2)) → i ≠ j → Fin n → Fin (n +ℕ 2)
skip-two-Fin' n i j i≠j k =
  let (j' , _) = fiber-skip-Fin (succ-ℕ n) i j i≠j
  in skip-Fin (succ-ℕ n) i (skip-Fin n j' k)

abstract opaque
  unfolding fiber-skip-Fin

  htpy-skip-two-Fin' :
    (n : ℕ) (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) →
    skip-two-Fin n i j i≠j ~ skip-two-Fin' n i j i≠j
  htpy-skip-two-Fin' (succ-ℕ n) (inl i) (inl j) i≠j (inl x) =
    ap inl (htpy-skip-two-Fin' n i j (nonequal-map inl i≠j) x)
  htpy-skip-two-Fin' (succ-ℕ n) (inl i) (inl j) i≠j (inr star) = refl
  htpy-skip-two-Fin' (succ-ℕ n) (inl i) (inr star) i≠j k = refl
  htpy-skip-two-Fin' (succ-ℕ n) (inr star) (inl j) i≠j k = refl
  htpy-skip-two-Fin' (succ-ℕ n) (inr star) (inr star) i≠j k =
    ex-falso (i≠j refl)
```

### `skip-two-Fin n i j i≠j` and `skip-two-Fin n j i j≠i` are homotopic

```agda
abstract
  swap-skip-two-Fin :
    (n : ℕ) (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (j≠i : j ≠ i) →
    skip-two-Fin n i j i≠j ~ skip-two-Fin n j i j≠i
  swap-skip-two-Fin (succ-ℕ n) (inl i) (inl j) i≠j j≠i (inl k) =
    ap
      ( inl)
      ( swap-skip-two-Fin n i j (nonequal-map inl i≠j) (nonequal-map inl j≠i) k)
  swap-skip-two-Fin (succ-ℕ n) (inl i) (inl j) i≠j j≠i (inr star) = refl
  swap-skip-two-Fin (succ-ℕ n) (inl i) (inr star) i≠j j≠i k = refl
  swap-skip-two-Fin (succ-ℕ n) (inr star) (inl j) i≠j j≠i k = refl
  swap-skip-two-Fin (succ-ℕ n) (inr star) (inr star) i≠j j≠i k =
    ex-falso (i≠j refl)
```

### `skip-two-Fin n i j i≠j k ≠ i`

```agda
abstract
  nonequal-left-skip-two-Fin :
    (n : ℕ) (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (k : Fin n) →
    skip-two-Fin n i j i≠j k ≠ i
  nonequal-left-skip-two-Fin (succ-ℕ n) (inl i) (inl j) i≠j (inl k) snijk=i =
    nonequal-left-skip-two-Fin
      ( n)
      ( i)
      ( j)
      ( nonequal-map inl i≠j)
      ( k)
      ( is-injective-inl snijk=i)
  nonequal-left-skip-two-Fin (succ-ℕ n) (inl i) (inr star) i≠j k snijk=i =
    nonequal-skip-Fin
      ( succ-ℕ n)
      ( i)
      ( k)
      ( is-injective-inl snijk=i)
  nonequal-left-skip-two-Fin (succ-ℕ n) (inr star) (inr star) i≠j =
    ex-falso (i≠j refl)
```

### `skip-two-Fin n i j i≠j k ≠ j`

```agda
abstract
  nonequal-right-skip-two-Fin :
    (n : ℕ) (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (k : Fin n) →
    skip-two-Fin n i j i≠j k ≠ j
  nonequal-right-skip-two-Fin (succ-ℕ n) (inl i) (inl j) i≠j (inl k) snijk=j =
    nonequal-right-skip-two-Fin
      ( n)
      ( i)
      ( j)
      ( nonequal-map inl i≠j)
      ( k)
      ( is-injective-inl snijk=j)
  nonequal-right-skip-two-Fin (succ-ℕ n) (inr star) (inl j) i≠j k snijk=j =
    nonequal-skip-Fin
      ( succ-ℕ n)
      ( j)
      ( k)
      ( is-injective-inl snijk=j)
  nonequal-right-skip-two-Fin (succ-ℕ n) (inr star) (inr star) i≠j =
    ex-falso (i≠j refl)
```

### Every element of `Fin (n + 2)` not equal to `i` or `j` is in the image of `skip-two-Fin n i j i≠j`

```agda
abstract
  fiber-skip-two-Fin :
    (n : ℕ) (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (k : Fin (n +ℕ 2)) →
    i ≠ k → j ≠ k → fiber (skip-two-Fin n i j i≠j) k
  fiber-skip-two-Fin n i j i≠j k i≠k j≠k =
    let
      (j' , snij'=j) = fiber-skip-Fin (succ-ℕ n) i j i≠j
      (k' , snik'=k) = fiber-skip-Fin (succ-ℕ n) i k i≠k
      (k'' , snj'k''=k') =
        fiber-skip-Fin n j' k'
          ( λ j'=k' →
            j≠k (inv snij'=j ∙ ap (skip-Fin (succ-ℕ n) i) j'=k' ∙ snik'=k))
    in
      ( k'' ,
        ( ( htpy-skip-two-Fin' n i j i≠j k'') ∙
          ( ap (skip-Fin (succ-ℕ n) i) snj'k''=k') ∙
          ( snik'=k)))
```
