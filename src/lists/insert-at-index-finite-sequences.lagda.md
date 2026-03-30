# Inserting elements in finite sequences

```agda
module lists.insert-at-index-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.functoriality-finite-sequences
open import lists.remove-at-index-finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `n : ℕ`
and a type `A`, the
{{#concept "insertion map" Disambiguation="of finite sequences" Agda=insert-at-fin-sequence}}
of an element `x : A` at an
[index](univalent-combinatorics.standard-finite-types.md) `i : Fin (n+1)` is the
map `Aⁿ → Aⁿ⁺¹` that **inserts** `x` at the `i`th coordinate:

```text
  (x₀,...xᵢ₋₁,xᵢ₊₁,...,xₙ) ↦ (x₀,...xᵢ₋₁,x,xᵢ₊₁,...,xₙ)
```

## Definitions

### Insertion at an index

```agda
module _
  {l : Level} {A : UU l}
  where

  insert-at-fin-sequence :
    (n : ℕ) →
    (a : A) →
    (i : Fin (succ-ℕ n)) →
    fin-sequence A n →
    fin-sequence A (succ-ℕ n)
  insert-at-fin-sequence zero-ℕ a _ _ _ = a
  insert-at-fin-sequence (succ-ℕ n) a (inl x) u (inl y) =
    insert-at-fin-sequence n a x (tail-fin-sequence n u) y
  insert-at-fin-sequence (succ-ℕ n) a (inl x) u (inr y) =
    head-fin-sequence n u
  insert-at-fin-sequence (succ-ℕ n) a (inr x) u (inl y) =
    elem-at-fin-sequence (succ-ℕ n) y u
  insert-at-fin-sequence (succ-ℕ n) a (inr x) u (inr y) = a
```

## Properties

### The coordinate at the index of an inserted element is the inserted element

```agda
module _
  {l : Level} {A : UU l}
  where

  compute-elem-at-insert-at-fin-sequence :
    (n : ℕ) →
    (a : A) →
    (i : Fin (succ-ℕ n)) →
    (u : fin-sequence A n) →
    elem-at-fin-sequence (succ-ℕ n) i (insert-at-fin-sequence n a i u) ＝
    a
  compute-elem-at-insert-at-fin-sequence zero-ℕ a _ _ = refl
  compute-elem-at-insert-at-fin-sequence (succ-ℕ n) a (inl x) u =
    compute-elem-at-insert-at-fin-sequence n a x (tail-fin-sequence n u)
  compute-elem-at-insert-at-fin-sequence (succ-ℕ n) a (inr x) u = refl
```

### Insertion is functorial

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  htpy-map-insert-at-fin-sequence :
    (n : ℕ) →
    (x : A) →
    (i : Fin (succ-ℕ n)) →
    (u : fin-sequence A n) →
    insert-at-fin-sequence n
      ( f x)
      ( i)
      ( map-fin-sequence n f u) ~
    map-fin-sequence (succ-ℕ n) f (insert-at-fin-sequence n x i u)
  htpy-map-insert-at-fin-sequence zero-ℕ x _ u _ = refl
  htpy-map-insert-at-fin-sequence (succ-ℕ n) x (inl i) u (inl j) =
    htpy-map-insert-at-fin-sequence n x i (tail-fin-sequence n u) j
  htpy-map-insert-at-fin-sequence (succ-ℕ n) x (inl i) u (inr j) = refl
  htpy-map-insert-at-fin-sequence (succ-ℕ n) x (inr _) u (inl j) = refl
  htpy-map-insert-at-fin-sequence (succ-ℕ n) x (inr _) u (inr j) = refl
```

### Inserting a removed an element produces is the identity

```agda
module _
  {l : Level} {A : UU l}
  where

  compute-insert-at-remove-at-fin-sequence :
    (n : ℕ) →
    (i : Fin (succ-ℕ n)) →
    (u : fin-sequence A (succ-ℕ n)) →
    insert-at-fin-sequence
      ( n)
      ( elem-at-fin-sequence (succ-ℕ n) i u)
      ( i)
      ( remove-at-fin-sequence n i u) ~
    u
  compute-insert-at-remove-at-fin-sequence zero-ℕ (inr _) u (inr _) = refl
  compute-insert-at-remove-at-fin-sequence (succ-ℕ n) (inl x) u (inl y) =
    compute-insert-at-remove-at-fin-sequence
      ( n)
      ( x)
      ( tail-fin-sequence (succ-ℕ n) u)
      ( y)
  compute-insert-at-remove-at-fin-sequence (succ-ℕ n) (inl x) u (inr y) = refl
  compute-insert-at-remove-at-fin-sequence (succ-ℕ n) (inr x) u (inl y) = refl
  compute-insert-at-remove-at-fin-sequence (succ-ℕ n) (inr x) u (inr y) = refl
```

### Removing an inserted element is the identity

```agda
module _
  {l : Level} {A : UU l}
  where

  compute-remove-at-insert-at-fin-sequence :
    (n : ℕ) →
    (a : A) →
    (i : Fin (succ-ℕ n)) →
    (u : fin-sequence A n) →
    remove-at-fin-sequence
      ( n)
      ( i)
      ( insert-at-fin-sequence n a i u) ~
    u
  compute-remove-at-insert-at-fin-sequence (succ-ℕ n) a (inl x) u (inl y) =
    compute-remove-at-insert-at-fin-sequence
      ( n)
      ( a)
      ( x)
      ( tail-fin-sequence n u)
      ( y)
  compute-remove-at-insert-at-fin-sequence (succ-ℕ n) a (inl x) u (inr y) = refl
  compute-remove-at-insert-at-fin-sequence (succ-ℕ n) a (inr x) u j = refl
```
