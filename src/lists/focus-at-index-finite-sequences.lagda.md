# Focus of finite sequences at an index

```agda
module lists.focus-at-index-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import lists.finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `n : ℕ`
and a type `A`, the [finite sequence](lists.finite-sequences.md) of
{{#concept "focusing maps" Disambiguation="of finite sequences" Agda=focus-at-finite-sequence}}
of `Aⁿ⁺¹` is the family of maps `(i : ℕₙ) → Aⁿ⁺¹ → A × Aⁿ`

```text
  (x₀,...xᵢ₋₁,xᵢ,xᵢ₊₁,...,xₙ) ↦ (xᵢ , (x₀,...xᵢ₋₁,xᵢ₊₁,...,xₙ))
```

## Definitions

### The coordinates maps

```agda
module _
  {l : Level} {A : UU l} (n : ℕ)
  where

  elem-at-fin-sequence : (i : Fin n) → fin-sequence A n → A
  elem-at-fin-sequence i v = v i
```

### Insertion at a index

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

### Dropping an element at an index

```agda
module _
  {l : Level} {A : UU l}
  where

  drop-at-fin-sequence :
    (n : ℕ) →
    (i : Fin (succ-ℕ n)) →
    fin-sequence A (succ-ℕ n) →
    fin-sequence A n
  drop-at-fin-sequence zero-ℕ _ u ()
  drop-at-fin-sequence (succ-ℕ n) (inl x) u (inl y) =
    drop-at-fin-sequence n x (tail-fin-sequence (succ-ℕ n) u) y
  drop-at-fin-sequence (succ-ℕ n) (inl x) u (inr y) =
    head-fin-sequence (succ-ℕ n) u
  drop-at-fin-sequence (succ-ℕ n) (inr x) u =
    tail-fin-sequence (succ-ℕ n) u
```

### Focusing a finite sequence at an index

```agda
module _
  {l : Level} {A : UU l} (n : ℕ) (i : Fin (succ-ℕ n))
  where

  focus-at-finite-sequence :
    fin-sequence A (succ-ℕ n) → A × fin-sequence A n
  focus-at-finite-sequence u =
    ( elem-at-fin-sequence (succ-ℕ n) i u ,
      drop-at-fin-sequence n i u)

  unfocus-at-finite-sequence :
    A × fin-sequence A n → fin-sequence A (succ-ℕ n)
  unfocus-at-finite-sequence (a , u) = insert-at-fin-sequence n a i u
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

### Inserting after dropping an element produces the original finite sequence

```agda
module _
  {l : Level} {A : UU l}
  where

  compute-insert-at-drop-at-fin-sequence :
    (n : ℕ) →
    (i : Fin (succ-ℕ n)) →
    (u : fin-sequence A (succ-ℕ n)) →
    insert-at-fin-sequence
      ( n)
      ( elem-at-fin-sequence (succ-ℕ n) i u)
      ( i)
      ( drop-at-fin-sequence n i u) ~
    u
  compute-insert-at-drop-at-fin-sequence zero-ℕ (inr _) u (inr _) = refl
  compute-insert-at-drop-at-fin-sequence (succ-ℕ n) (inl x) u (inl y) =
    compute-insert-at-drop-at-fin-sequence
      ( n)
      ( x)
      ( tail-fin-sequence (succ-ℕ n) u)
      ( y)
  compute-insert-at-drop-at-fin-sequence (succ-ℕ n) (inl x) u (inr y) = refl
  compute-insert-at-drop-at-fin-sequence (succ-ℕ n) (inr x) u (inl y) = refl
  compute-insert-at-drop-at-fin-sequence (succ-ℕ n) (inr x) u (inr y) = refl
```

### Dropping an inserted element produces the original finite sequence

```agda
module _
  {l : Level} {A : UU l}
  where

  compute-drop-at-insert-at-fin-sequence :
    (n : ℕ) →
    (a : A) →
    (i : Fin (succ-ℕ n)) →
    (u : fin-sequence A n) →
    drop-at-fin-sequence
      ( n)
      ( i)
      ( insert-at-fin-sequence n a i u) ~
    u
  compute-drop-at-insert-at-fin-sequence (succ-ℕ n) a (inl x) u (inl y) =
    compute-drop-at-insert-at-fin-sequence
      ( n)
      ( a)
      ( x)
      ( tail-fin-sequence n u)
      ( y)
  compute-drop-at-insert-at-fin-sequence (succ-ℕ n) a (inl x) u (inr y) = refl
  compute-drop-at-insert-at-fin-sequence (succ-ℕ n) a (inr x) u j = refl
```

### Focusing a finite sequence at an index is an equivalence

```agda
module _
  {l : Level} {A : UU l} (n : ℕ) (i : Fin (succ-ℕ n))
  where abstract

  is-section-focus-at-finite-sequence :
    (x : A × fin-sequence A n) →
    focus-at-finite-sequence n i (unfocus-at-finite-sequence n i x) ＝ x
  is-section-focus-at-finite-sequence (a , u) =
    eq-pair
      ( compute-elem-at-insert-at-fin-sequence n a i u)
      ( eq-htpy (compute-drop-at-insert-at-fin-sequence n a i u))

  is-retraction-focus-at-finite-sequence :
    (v : fin-sequence A (succ-ℕ n)) →
    unfocus-at-finite-sequence n i (focus-at-finite-sequence n i v) ＝ v
  is-retraction-focus-at-finite-sequence =
    eq-htpy ∘ compute-insert-at-drop-at-fin-sequence n i

  is-equiv-focus-at-finite-sequence :
    is-equiv (focus-at-finite-sequence {A = A} n i)
  is-equiv-focus-at-finite-sequence =
    is-equiv-is-invertible
      ( unfocus-at-finite-sequence n i)
      ( is-section-focus-at-finite-sequence)
      ( is-retraction-focus-at-finite-sequence)

module _
  {l : Level} (A : UU l) (n : ℕ) (i : Fin (succ-ℕ n))
  where

  equiv-focus-at-finite-sequence :
    fin-sequence A (succ-ℕ n) ≃ A × fin-sequence A n
  equiv-focus-at-finite-sequence =
    (focus-at-finite-sequence n i , is-equiv-focus-at-finite-sequence n i)
```
