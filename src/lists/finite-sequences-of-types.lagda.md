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
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
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
open import lists.insert-at-index-finite-sequences
open import lists.remove-at-index-finite-sequences
open import lists.sequences

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A [finite sequence](lists.finite-sequences.md) of types `A : Fin n → UU l`
induces a type `Πₙ A = (i : Fin n) → A i`, i.e.,

```text
  Πₙ A ≃ A₀ × A₁ × ... × Aᵢ × ... Aₙ₋₁
```

For any [natural number](elementary-number-theory.natural-numbers.md) `n`, and
and any [index](univalent-combinatorics.standard-finite-types.md)
`i : Fin (n+1)`,

```text
  Πₙ₊₁ A ≃ Aᵢ × Πₙ Aⁱ
```

where `Aⁱ` denotes the finite sequence of types obtained by
[removing](lists.remove-at-index-finite-sequences.md) the `i`th component of `A`
so `Πₙ Aⁱ = A₀ × ... Aᵢ₋₁ × Aᵢ₊ᵢ × ... × Aₙ`.

## Definition

### Elements of a finite product of types

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

### Removing at an index

```agda
remove-at-Π-fin-sequence :
  {l : Level} →
  (n : ℕ)
  (A : Fin (succ-ℕ n) → UU l) →
  (i : Fin (succ-ℕ n)) →
  Π-fin-sequence (succ-ℕ n) A →
  Π-fin-sequence n (remove-at-fin-sequence n i A)
remove-at-Π-fin-sequence zero-ℕ A (inr _) u ()
remove-at-Π-fin-sequence (succ-ℕ n) A (inl i) u (inl j) =
  remove-at-Π-fin-sequence
    ( n)
    ( tail-fin-sequence (succ-ℕ n) A)
    ( i)
    ( u ∘ inl-Fin (succ-ℕ n))
    ( j)
remove-at-Π-fin-sequence (succ-ℕ n) A (inl i) u (inr _) = u (inr _)
remove-at-Π-fin-sequence (succ-ℕ n) A (inr i) u j = u (inl j)
```

### Focusing at in index

```agda
focus-at-Π-fin-sequence :
  {l : Level} →
  (n : ℕ)
  (A : Fin (succ-ℕ n) → UU l) →
  (i : Fin (succ-ℕ n)) →
  Π-fin-sequence (succ-ℕ n) A →
  (A i × Π-fin-sequence n (remove-at-fin-sequence n i A))
focus-at-Π-fin-sequence n A i u =
  ( elem-at-Π-fin-sequence (succ-ℕ n) A i u ,
    remove-at-Π-fin-sequence n A i u)

unfocus-at-Π-fin-sequence :
  {l : Level} →
  (n : ℕ)
  (A : Fin (succ-ℕ n) → UU l) →
  (i : Fin (succ-ℕ n)) →
  (A i × Π-fin-sequence n (remove-at-fin-sequence n i A)) →
  Π-fin-sequence (succ-ℕ n) A
unfocus-at-Π-fin-sequence n A i (x , u) = insert-at-Π-fin-sequence n A i x u
```

### The coordinate at the index of an inserted element is the inserted element

```agda
compute-elem-at-insert-at-Π-fin-sequence :
  {l : Level} →
  (n : ℕ) →
  (A : Fin (succ-ℕ n) → UU l) →
  (i : Fin (succ-ℕ n)) →
  (x : A i) →
  (u : Π-fin-sequence n (remove-at-fin-sequence n i A)) →
  elem-at-Π-fin-sequence (succ-ℕ n) A i (insert-at-Π-fin-sequence n A i x u) ＝
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

### Inserting a removed element is the identity

```agda
compute-insert-at-remove-at-Π-fin-sequence :
  {l : Level} →
  (n : ℕ) →
  (A : Fin (succ-ℕ n) → UU l) →
  (i : Fin (succ-ℕ n)) →
  (u : Π-fin-sequence (succ-ℕ n) A) →
  insert-at-Π-fin-sequence
    ( n)
    ( A)
    ( i)
    ( elem-at-Π-fin-sequence (succ-ℕ n) A i u)
    ( remove-at-Π-fin-sequence n A i u) ~
  u
compute-insert-at-remove-at-Π-fin-sequence zero-ℕ A (inr _) u (inr _) = refl
compute-insert-at-remove-at-Π-fin-sequence (succ-ℕ n) A (inl i) u (inl j) =
  compute-insert-at-remove-at-Π-fin-sequence
    ( n)
    ( tail-fin-sequence (succ-ℕ n) A)
    ( i)
    ( u ∘ inl-Fin (succ-ℕ n))
    ( j)
compute-insert-at-remove-at-Π-fin-sequence (succ-ℕ n) A (inl i) u (inr j) = refl
compute-insert-at-remove-at-Π-fin-sequence (succ-ℕ n) A (inr i) u (inl j) = refl
compute-insert-at-remove-at-Π-fin-sequence (succ-ℕ n) A (inr i) u (inr j) = refl
```

### Removing an inserted element is the identity

```agda
compute-remove-at-insert-at-Π-fin-sequence :
  {l : Level} →
  (n : ℕ) →
  (A : Fin (succ-ℕ n) → UU l) →
  (i : Fin (succ-ℕ n)) →
  (x : A i) →
  (u : Π-fin-sequence n (remove-at-fin-sequence n i A)) →
  remove-at-Π-fin-sequence
    ( n)
    ( A)
    ( i)
    ( insert-at-Π-fin-sequence n A i x u) ~
  u
compute-remove-at-insert-at-Π-fin-sequence zero-ℕ A i x u ()
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

### Focusing a finite sequence at an index is an equivalence

```agda
module _
  {l : Level}
  (n : ℕ)
  (A : Fin (succ-ℕ n) → UU l)
  (i : Fin (succ-ℕ n))
  where abstract

  is-section-focus-at-Π-finite-sequence :
    focus-at-Π-fin-sequence n A i ∘ unfocus-at-Π-fin-sequence n A i ~ id
  is-section-focus-at-Π-finite-sequence (x , u) =
    eq-pair
      ( compute-elem-at-insert-at-Π-fin-sequence n A i x u)
      ( eq-htpy (compute-remove-at-insert-at-Π-fin-sequence n A i x u))

  is-retraction-focus-at-Π-finite-sequence :
    unfocus-at-Π-fin-sequence n A i ∘ focus-at-Π-fin-sequence n A i ~ id
  is-retraction-focus-at-Π-finite-sequence =
    eq-htpy ∘ compute-insert-at-remove-at-Π-fin-sequence n A i

  is-equiv-focus-at-Π-finite-sequence :
    is-equiv (focus-at-Π-fin-sequence n A i)
  is-equiv-focus-at-Π-finite-sequence =
    is-equiv-is-invertible
      ( unfocus-at-Π-fin-sequence n A i)
      ( is-section-focus-at-Π-finite-sequence)
      ( is-retraction-focus-at-Π-finite-sequence)

module _
  {l : Level}
  (n : ℕ)
  (A : Fin (succ-ℕ n) → UU l)
  where

  Π-equiv-focus-at-Π-fin-sequence :
    Π-fin-sequence
      ( succ-ℕ n)
      ( λ i →
        Π-fin-sequence (succ-ℕ n) A ≃
        A i × Π-fin-sequence n (remove-at-fin-sequence n i A))
  Π-equiv-focus-at-Π-fin-sequence i =
    ( focus-at-Π-fin-sequence n A i ,
      is-equiv-focus-at-Π-finite-sequence n A i)
```
