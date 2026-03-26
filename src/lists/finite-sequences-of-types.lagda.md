# Finite sequences of types

```agda
module lists.finite-sequences-of-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.focus-at-index-finite-sequences
open import lists.sequences

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An [finite sequence](lists.finite-sequences.md) of types `A : Fin n → UU l`
induces a type `Πₙ A = (i : Fin n) → A i`.

For any [natural number](elementary-number-theory.natural-numbers.md) `n`, and
and any [index](univalent-combinatorics.standard-finite-types.md) `i : ℕₙ`,

```text
  Πₙ₊₁ A ≃ A i × Πₙ Aⁱ
```

where `Aⁱ` denotes the finite sequence of types obtained by
[dropping](lists.focus-at-index-finite-sequences.md) the `i`th component of `A`.

## Definition

### Elements of a finite products of types

```agda
module _
  {l : Level} (n : ℕ) (A : Fin n → UU l)
  where

  Π-fin-sequence : UU l
  Π-fin-sequence = (i : Fin n) → A i
```

## Properties

### Coordinate maps of finite products

```agda
module _
  {l : Level} (n : ℕ) (A : Fin n → UU l)
  where

  elem-at-Π-fin-sequence :
    (i : Fin n) → Π-fin-sequence n A → A i
  elem-at-Π-fin-sequence i u = u i
```

### Insertion at an index

```agda
insert-at-Π-fin-sequence :
  {l : Level} →
  (n : ℕ) →
  (A : Fin (succ-ℕ n) → UU l) →
  (i : Fin (succ-ℕ n)) →
  (x : A i) →
  Π-fin-sequence n (drop-at-fin-sequence n i A) →
  Π-fin-sequence (succ-ℕ n) A
insert-at-Π-fin-sequence zero-ℕ A (inr _) x _ (inr _) = x
insert-at-Π-fin-sequence (succ-ℕ n) A (inl i) x u (inl j) =
  insert-at-Π-fin-sequence
    ( n)
    ( tail-fin-sequence (succ-ℕ n) A)
    ( i)
    ( x)
    ( u ∘ (inl-Fin n))
    ( j)
insert-at-Π-fin-sequence (succ-ℕ n) A (inl i) x u (inr j) = u (inr j)
insert-at-Π-fin-sequence (succ-ℕ n) A (inr i) x u (inl j) = u j
insert-at-Π-fin-sequence (succ-ℕ n) A (inr i) x u (inr j) = x
```

### Dropping at an index

```agda
drop-at-Π-fin-sequence :
  {l : Level} →
  (n : ℕ)
  (A : Fin (succ-ℕ n) → UU l) →
  (i : Fin (succ-ℕ n)) →
  Π-fin-sequence (succ-ℕ n) A →
  Π-fin-sequence n (drop-at-fin-sequence n i A)
drop-at-Π-fin-sequence zero-ℕ A (inr _) u ()
drop-at-Π-fin-sequence (succ-ℕ n) A (inl i) u (inl j) =
  drop-at-Π-fin-sequence
    ( n)
    ( tail-fin-sequence (succ-ℕ n) A)
    ( i)
    ( u ∘ inl-Fin (succ-ℕ n))
    ( j)
drop-at-Π-fin-sequence (succ-ℕ n) A (inl i) u (inr _) = u (inr _)
drop-at-Π-fin-sequence (succ-ℕ n) A (inr i) u j = u (inl j)
```

### Focusing at in index

```agda
focus-at-Π-fin-sequence :
  {l : Level} →
  (n : ℕ)
  (A : Fin (succ-ℕ n) → UU l) →
  (i : Fin (succ-ℕ n)) →
  Π-fin-sequence (succ-ℕ n) A →
  (A i × Π-fin-sequence n (drop-at-fin-sequence n i A))
focus-at-Π-fin-sequence n A i u =
  ( elem-at-Π-fin-sequence (succ-ℕ n) A i u ,
    drop-at-Π-fin-sequence n A i u)

unfocus-at-Π-fin-sequence :
  {l : Level} →
  (n : ℕ)
  (A : Fin (succ-ℕ n) → UU l) →
  (i : Fin (succ-ℕ n)) →
  (A i × Π-fin-sequence n (drop-at-fin-sequence n i A)) →
  Π-fin-sequence (succ-ℕ n) A
unfocus-at-Π-fin-sequence n A i (x , u) = insert-at-Π-fin-sequence n A i x u
```

-- TODO Prove that this is an equivalence
