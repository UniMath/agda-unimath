# Inserting elements in finite sequences of types

```agda
{-# OPTIONS --lossy-unification #-}

module lists.insert-at-index-finite-sequences-of-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.finite-sequences-of-types
open import lists.remove-at-index-finite-sequences
open import lists.remove-at-index-finite-sequences-of-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `n` and a
[finite sequence of types](lists.finite-sequences-of-types.md) `A₀, ..., Aₙ`,
the
{{#concept "insertion map" Disambiguation="of dependent finite sequences" Agda=insert-at-Π-fin-sequence}}
of an element `x : A` at an
[index](univalent-combinatorics.standard-finite-types.md) `i : Fin (n+1)` is the
map taking an element of `Πᵢ Aᵢ` that **inserts** `x` at the `i`th coordinate:

```text
  (x₀,...xᵢ₋₁,xᵢ₊₁,...,xₙ) ↦ (x₀,...xᵢ₋₁,x,xᵢ₊₁,...,xₙ)
```

## Definition

### Inserting at one index

```agda
insert-at-Π-fin-sequence :
  {l : Level} (n : ℕ) (A : fin-sequence (UU l) (succ-ℕ n))
  (i : Fin (succ-ℕ n)) (x : A i) →
  Π-fin-sequence n (remove-at-fin-sequence n i A) →
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

### Inserting at two indices

```agda
insert-at-two-indices-Π-fin-sequence :
  {l : Level} (n : ℕ) (A : fin-sequence (UU l) (n +ℕ 2))
  (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) → A i → A j →
  Π-fin-sequence n (remove-at-two-indices-fin-sequence n i j i≠j A) →
  Π-fin-sequence (n +ℕ 2) A
insert-at-two-indices-Π-fin-sequence n A (inr star) (inr star) i≠j uᵢ uⱼ u k =
  ex-falso (i≠j refl)
insert-at-two-indices-Π-fin-sequence
  n A (inr star) (inl j) i≠j uᵢ uⱼ u (inr star) =
  uᵢ
insert-at-two-indices-Π-fin-sequence
  n A (inl i) (inr star) i≠j uᵢ uⱼ u (inr star) =
  uⱼ
insert-at-two-indices-Π-fin-sequence
  zero-ℕ A (inl (inr star)) (inr star) i≠j uᵢ uⱼ u (inl (inr star)) =
  uᵢ
insert-at-two-indices-Π-fin-sequence
  zero-ℕ A (inr star) (inl (inr star)) i≠j uᵢ uⱼ u (inl (inr star)) =
  uⱼ
insert-at-two-indices-Π-fin-sequence
  zero-ℕ A (inl (inr star)) (inl (inr star)) i≠j =
  ex-falso (i≠j refl)
insert-at-two-indices-Π-fin-sequence
  (succ-ℕ n) A (inl i) (inl j) i≠j uᵢ uⱼ u (inl k) =
  insert-at-two-indices-Π-fin-sequence
    ( n)
    ( tail-fin-sequence (n +ℕ 2) A)
    ( i)
    ( j)
    ( nonequal-map inl i≠j)
    ( uᵢ)
    ( uⱼ)
    ( u ∘ inl-Fin n)
    ( k)
insert-at-two-indices-Π-fin-sequence
  (succ-ℕ n) A (inl i) (inl j) i≠j uᵢ uⱼ u (inr star) =
  u (inr star)
insert-at-two-indices-Π-fin-sequence
  (succ-ℕ n) A (inl i) (inr star) i≠j uᵢ uⱼ u (inl k) =
  insert-at-Π-fin-sequence
    ( succ-ℕ n)
    ( A ∘ inl-Fin (n +ℕ 2))
    ( i)
    ( uᵢ)
    ( u)
    ( k)
insert-at-two-indices-Π-fin-sequence
  (succ-ℕ n) A (inr star) (inl j) i≠j uᵢ uⱼ u (inl k) =
  insert-at-Π-fin-sequence
    ( succ-ℕ n)
    ( A ∘ inl-Fin (n +ℕ 2))
    ( j)
    ( uⱼ)
    ( u)
    ( k)
```

## Properties

### The coordinate at the index of an inserted element is the inserted element

```agda
abstract
  compute-elem-at-insert-at-Π-fin-sequence :
    {l : Level} (n : ℕ) (A : fin-sequence (UU l) (succ-ℕ n))
    (i : Fin (succ-ℕ n)) (x : A i)
    (u : Π-fin-sequence n (remove-at-fin-sequence n i A)) →
    elem-at-Π-fin-sequence (succ-ℕ n) A i
      ( insert-at-Π-fin-sequence n A i x u) ＝
    x
  compute-elem-at-insert-at-Π-fin-sequence zero-ℕ A (inr _) x u = refl
  compute-elem-at-insert-at-Π-fin-sequence (succ-ℕ n) A (inl i) x u =
    compute-elem-at-insert-at-Π-fin-sequence
      ( n)
      ( tail-fin-sequence (succ-ℕ n) A)
      ( i)
      ( x)
      ( u ∘ inl-Fin n)
  compute-elem-at-insert-at-Π-fin-sequence (succ-ℕ n) A (inr i) x u = refl
```

### The coordinate at the first of two inserted indices is the inserted element

```agda
abstract
  compute-first-elem-at-insert-at-two-indices-Π-fin-sequence :
    {l : Level} (n : ℕ) (A : fin-sequence (UU l) (n +ℕ 2)) →
    (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (uᵢ : A i) (uⱼ : A j) →
    (u : Π-fin-sequence n (remove-at-two-indices-fin-sequence n i j i≠j A)) →
    insert-at-two-indices-Π-fin-sequence n A i j i≠j uᵢ uⱼ u i ＝ uᵢ
  compute-first-elem-at-insert-at-two-indices-Π-fin-sequence
    n A (inr star) (inr star) i≠j uᵢ uⱼ u =
    ex-falso (i≠j refl)
  compute-first-elem-at-insert-at-two-indices-Π-fin-sequence
    zero-ℕ A (inl (inr star)) (inl (inr star)) i≠j uᵢ uⱼ u =
    ex-falso (i≠j refl)
  compute-first-elem-at-insert-at-two-indices-Π-fin-sequence
    zero-ℕ A (inl (inr star)) (inr star) i≠j uᵢ uⱼ u =
    refl
  compute-first-elem-at-insert-at-two-indices-Π-fin-sequence
    zero-ℕ A (inr star) (inl (inr star)) i≠j uᵢ uⱼ u =
    refl
  compute-first-elem-at-insert-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inl i) (inl j) i≠j uᵢ uⱼ u =
    compute-first-elem-at-insert-at-two-indices-Π-fin-sequence
      ( n)
      ( tail-fin-sequence (n +ℕ 2) A)
      ( i)
      ( j)
      ( nonequal-map inl i≠j)
      ( uᵢ)
      ( uⱼ)
      ( u ∘ inl)
  compute-first-elem-at-insert-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inl i) (inr star) i≠j uᵢ uⱼ u =
    compute-elem-at-insert-at-Π-fin-sequence
      ( succ-ℕ n)
      ( tail-fin-sequence (n +ℕ 2) A)
      ( i)
      ( uᵢ)
      ( u)
  compute-first-elem-at-insert-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inr star) (inl j) i≠j uᵢ uⱼ u =
    refl
```

### The coordinate at the second of two inserted indices is the second element

```agda
abstract
  compute-second-elem-at-insert-at-two-indices-Π-fin-sequence :
    {l : Level} (n : ℕ) (A : fin-sequence (UU l) (n +ℕ 2)) →
    (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (uᵢ : A i) (uⱼ : A j) →
    (u : Π-fin-sequence n (remove-at-two-indices-fin-sequence n i j i≠j A)) →
    insert-at-two-indices-Π-fin-sequence n A i j i≠j uᵢ uⱼ u j ＝ uⱼ
  compute-second-elem-at-insert-at-two-indices-Π-fin-sequence
    n A (inr star) (inr star) i≠j =
    ex-falso (i≠j refl)
  compute-second-elem-at-insert-at-two-indices-Π-fin-sequence
    zero-ℕ A (inl (inr star)) (inl (inr star)) i≠j =
    ex-falso (i≠j refl)
  compute-second-elem-at-insert-at-two-indices-Π-fin-sequence
    zero-ℕ A (inl (inr star)) (inr star) i≠j uᵢ uⱼ u =
    refl
  compute-second-elem-at-insert-at-two-indices-Π-fin-sequence
    zero-ℕ A (inr star) (inl (inr star)) i≠j uᵢ uⱼ u =
    refl
  compute-second-elem-at-insert-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inl i) (inl j) i≠j uᵢ uⱼ u =
    compute-second-elem-at-insert-at-two-indices-Π-fin-sequence
      ( n)
      ( tail-fin-sequence (n +ℕ 2) A)
      ( i)
      ( j)
      ( nonequal-map inl i≠j)
      ( uᵢ)
      ( uⱼ)
      ( u ∘ inl)
  compute-second-elem-at-insert-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inr star) (inl j) i≠j uᵢ uⱼ u =
    compute-elem-at-insert-at-Π-fin-sequence
      ( succ-ℕ n)
      ( tail-fin-sequence (n +ℕ 2) A)
      ( j)
      ( uⱼ)
      ( u)
  compute-second-elem-at-insert-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inl i) (inr star) i≠j uᵢ uⱼ u =
    refl
```

### Inserting a removed element is the identity

```agda
abstract
  compute-insert-at-remove-at-Π-fin-sequence :
    {l : Level} (n : ℕ) (A : fin-sequence (UU l) (succ-ℕ n))
    (i : Fin (succ-ℕ n)) (u : Π-fin-sequence (succ-ℕ n) A) →
    insert-at-Π-fin-sequence
      ( n)
      ( A)
      ( i)
      ( elem-at-Π-fin-sequence (succ-ℕ n) A i u)
      ( remove-at-Π-fin-sequence n A i u) ~
    u
  compute-insert-at-remove-at-Π-fin-sequence zero-ℕ A (inr _) u (inr _) =
    refl
  compute-insert-at-remove-at-Π-fin-sequence (succ-ℕ n) A (inl i) u (inl j) =
    compute-insert-at-remove-at-Π-fin-sequence
      ( n)
      ( tail-fin-sequence (succ-ℕ n) A)
      ( i)
      ( u ∘ inl-Fin (succ-ℕ n))
      ( j)
  compute-insert-at-remove-at-Π-fin-sequence (succ-ℕ n) A (inl i) u (inr j) =
    refl
  compute-insert-at-remove-at-Π-fin-sequence (succ-ℕ n) A (inr i) u (inl j) =
    refl
  compute-insert-at-remove-at-Π-fin-sequence (succ-ℕ n) A (inr i) u (inr j) =
    refl
```

### Removing an inserted element is the identity

```agda
abstract
  compute-remove-at-insert-at-Π-fin-sequence :
    {l : Level} (n : ℕ) (A : fin-sequence (UU l) (succ-ℕ n)) →
    (i : Fin (succ-ℕ n)) (x : A i)
    (u : Π-fin-sequence n (remove-at-fin-sequence n i A)) →
    remove-at-Π-fin-sequence n A i (insert-at-Π-fin-sequence n A i x u) ~ u
  compute-remove-at-insert-at-Π-fin-sequence (succ-ℕ n) A (inl i) x u (inl j) =
    compute-remove-at-insert-at-Π-fin-sequence
      ( n)
      ( tail-fin-sequence (succ-ℕ n) A)
      ( i)
      ( x)
      ( u ∘ inl-Fin n)
      ( j)
  compute-remove-at-insert-at-Π-fin-sequence (succ-ℕ n) A (inl i) x u (inr j) =
    refl
  compute-remove-at-insert-at-Π-fin-sequence (succ-ℕ n) A (inr i) x u j = refl
```

### Inserting two removed elements is the identity

```agda
abstract
  compute-insert-at-remove-at-two-indices-Π-fin-sequence :
    {l : Level} (n : ℕ) (A : fin-sequence (UU l) (n +ℕ 2))
    (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (u : Π-fin-sequence (n +ℕ 2) A) →
    insert-at-two-indices-Π-fin-sequence
      ( n)
      ( A)
      ( i)
      ( j)
      ( i≠j)
      ( u i)
      ( u j)
      ( remove-at-two-indices-Π-fin-sequence n A i j i≠j u) ~ u
  compute-insert-at-remove-at-two-indices-Π-fin-sequence
    n A (inr star) (inr star) i≠j =
    ex-falso (i≠j refl)
  compute-insert-at-remove-at-two-indices-Π-fin-sequence
    n A (inr star) (inl j) i≠j u (inr star) =
    refl
  compute-insert-at-remove-at-two-indices-Π-fin-sequence
    n A (inl i) (inr star) i≠j u (inr star) =
    refl
  compute-insert-at-remove-at-two-indices-Π-fin-sequence
    zero-ℕ A (inl (inr star)) (inr star) i≠j u (inl (inr star)) =
    refl
  compute-insert-at-remove-at-two-indices-Π-fin-sequence
    zero-ℕ A (inr star) (inl (inr star)) i≠j u (inl (inr star)) =
    refl
  compute-insert-at-remove-at-two-indices-Π-fin-sequence
    zero-ℕ A (inl (inr star)) (inl (inr star)) i≠j =
    ex-falso (i≠j refl)
  compute-insert-at-remove-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inl i) (inl j) i≠j u (inl k) =
    compute-insert-at-remove-at-two-indices-Π-fin-sequence
      ( n)
      ( tail-fin-sequence (n +ℕ 2) A)
      ( i)
      ( j)
      ( nonequal-map inl i≠j)
      ( u ∘ inl)
      ( k)
  compute-insert-at-remove-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inl i) (inl j) i≠j u (inr star) =
    refl
  compute-insert-at-remove-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inl i) (inr star) i≠j u (inl k) =
    compute-insert-at-remove-at-Π-fin-sequence
      ( succ-ℕ n)
      ( tail-fin-sequence (n +ℕ 2) A)
      ( i)
      ( u ∘ inl)
      ( k)
  compute-insert-at-remove-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inr star) (inl j) i≠j u (inl k) =
    compute-insert-at-remove-at-Π-fin-sequence
      ( succ-ℕ n)
      ( tail-fin-sequence (n +ℕ 2) A)
      ( j)
      ( u ∘ inl)
      ( k)
```

### Removing two inserted elements is the identity

```agda
abstract
  compute-remove-at-insert-at-two-indices-Π-fin-sequence :
    {l : Level} (n : ℕ) (A : fin-sequence (UU l) (n +ℕ 2)) →
    (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (uᵢ : A i) (uⱼ : A j) →
    (u : Π-fin-sequence n (remove-at-two-indices-fin-sequence n i j i≠j A)) →
    remove-at-two-indices-Π-fin-sequence n A i j i≠j
      ( insert-at-two-indices-Π-fin-sequence n A i j i≠j uᵢ uⱼ u) ~
    u
  compute-remove-at-insert-at-two-indices-Π-fin-sequence
    n A (inr star) (inr star) i≠j =
    ex-falso (i≠j refl)
  compute-remove-at-insert-at-two-indices-Π-fin-sequence
    zero-ℕ A (inl (inr star)) (inl (inr star)) i≠j =
    ex-falso (i≠j refl)
  compute-remove-at-insert-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inl i) (inl j) i≠j uᵢ uⱼ u (inl k) =
    compute-remove-at-insert-at-two-indices-Π-fin-sequence
      ( n)
      ( tail-fin-sequence (n +ℕ 2) A)
      ( i)
      ( j)
      ( nonequal-map inl i≠j)
      ( uᵢ)
      ( uⱼ)
      ( u ∘ inl)
      ( k)
  compute-remove-at-insert-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inl i) (inl j) i≠j uᵢ uⱼ u (inr star) =
    refl
  compute-remove-at-insert-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inr star) (inl j) i≠j uᵢ uⱼ u k =
    compute-remove-at-insert-at-Π-fin-sequence
      ( succ-ℕ n)
      ( tail-fin-sequence (n +ℕ 2) A)
      ( j)
      ( uⱼ)
      ( u)
      ( k)
  compute-remove-at-insert-at-two-indices-Π-fin-sequence
    (succ-ℕ n) A (inl i) (inr star) i≠j uᵢ uⱼ u k =
    compute-remove-at-insert-at-Π-fin-sequence
      ( succ-ℕ n)
      ( tail-fin-sequence (n +ℕ 2) A)
      ( i)
      ( uᵢ)
      ( u)
      ( k)
```
