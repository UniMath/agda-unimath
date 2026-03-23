# Finite sequences

```agda
module lists.finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
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

open import lists.sequences

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A {{#concept "finite sequence" WD="n-tuple" WDID=Q600590 Agda=fin-sequence}} of
length `n` is a map from the
[standard finite type](univalent-combinatorics.standard-finite-types.md) of
cardinality `n`, `Fin n`, to `A`. These are
[equivalent](lists.equivalence-tuples-finite-sequences.md) to the related
concept of [tuples](lists.tuples.md), but are structured like
[arrays](lists.arrays.md) instead of [lists](lists.lists.md).

## Definition

```agda
fin-sequence : {l : Level} → UU l → ℕ → UU l
fin-sequence A n = Fin n → A

module _
  {l : Level} {A : UU l}
  where

  empty-fin-sequence : fin-sequence A 0
  empty-fin-sequence ()

  head-fin-sequence : (n : ℕ) → fin-sequence A (succ-ℕ n) → A
  head-fin-sequence n v = v (inr star)

  tail-fin-sequence :
    (n : ℕ) → fin-sequence A (succ-ℕ n) → fin-sequence A n
  tail-fin-sequence n v = v ∘ (inl-Fin n)

  cons-fin-sequence :
    (n : ℕ) → A → fin-sequence A n → fin-sequence A (succ-ℕ n)
  cons-fin-sequence n a v (inl x) = v x
  cons-fin-sequence n a v (inr x) = a

  snoc-fin-sequence :
    (n : ℕ) → fin-sequence A n → A → fin-sequence A (succ-ℕ n)
  snoc-fin-sequence zero-ℕ v a i = a
  snoc-fin-sequence (succ-ℕ n) v a (inl x) =
    snoc-fin-sequence n (tail-fin-sequence n v) a x
  snoc-fin-sequence (succ-ℕ n) v a (inr x) = head-fin-sequence n v

  revert-fin-sequence :
    (n : ℕ) → fin-sequence A n → fin-sequence A n
  revert-fin-sequence n v i = v (opposite-Fin n i)

  in-fin-sequence : (n : ℕ) → A → fin-sequence A n → UU l
  in-fin-sequence n a v = Σ (Fin n) (λ k → a ＝ v k)

  index-in-fin-sequence :
    (n : ℕ) (x : A) (v : fin-sequence A n) →
    in-fin-sequence n x v → Fin n
  index-in-fin-sequence n x v I = pr1 I

  eq-component-fin-sequence-index-in-fin-sequence :
    (n : ℕ) (x : A) (v : fin-sequence A n) (I : in-fin-sequence n x v) →
    x ＝ v (index-in-fin-sequence n x v I)
  eq-component-fin-sequence-index-in-fin-sequence n x v I = pr2 I
```

## Operations

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

### Swapping elements at a pair of indices

```agda
module _
  {l : Level} {A : UU l} (n : ℕ) (i j : Fin (succ-ℕ n))
  where

  swap-at-finite-sequence :
    fin-sequence A (succ-ℕ n) → fin-sequence A (succ-ℕ n)
  swap-at-finite-sequence =
    unfocus-at-finite-sequence n i ∘ focus-at-finite-sequence n j
```

## Properties

### The type of finite sequences of elements in a truncated type is truncated

```agda
module _
  {l : Level} {A : UU l}
  where

  is-trunc-fin-sequence :
    (k : 𝕋) (n : ℕ) → is-trunc k A → is-trunc k (fin-sequence A n)
  is-trunc-fin-sequence k n H = is-trunc-function-type k H
```

### The type of finite sequences of elements in a set is a set

```agda
module _
  {l : Level} {A : UU l}
  where

  is-set-fin-sequence : (n : ℕ) → is-set A → is-set (fin-sequence A n)
  is-set-fin-sequence = is-trunc-fin-sequence zero-𝕋

fin-sequence-Set : {l : Level} → Set l → ℕ → Set l
pr1 (fin-sequence-Set A n) = fin-sequence (type-Set A) n
pr2 (fin-sequence-Set A n) = is-set-fin-sequence n (is-set-type-Set A)
```

### Adding the tail to the head gives the same finite sequence

```agda
module _
  {l : Level} {A : UU l}
  where
  htpy-cons-head-tail-fin-sequence :
    ( n : ℕ) →
    ( v : fin-sequence A (succ-ℕ n)) →
    ( cons-fin-sequence n
      ( head-fin-sequence n v)
      ( tail-fin-sequence n v)) ~
      ( v)
  htpy-cons-head-tail-fin-sequence n v (inl x) = refl
  htpy-cons-head-tail-fin-sequence n v (inr star) = refl

  cons-head-tail-fin-sequence :
    ( n : ℕ) →
    ( v : fin-sequence A (succ-ℕ n)) →
    ( cons-fin-sequence n
      ( head-fin-sequence n v)
      ( tail-fin-sequence n v)) ＝
      ( v)
  cons-head-tail-fin-sequence n v =
    eq-htpy (htpy-cons-head-tail-fin-sequence n v)
```

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

### Swapping elements is an equivalence

```agda
module _
  {l : Level} {A : UU l} (n : ℕ)
  where abstract

  is-section-swap-at-finite-sequence :
    (i j : Fin (succ-ℕ n)) →
    (u : fin-sequence A (succ-ℕ n)) →
    swap-at-finite-sequence n i j (swap-at-finite-sequence n j i u) ＝ u
  is-section-swap-at-finite-sequence i j u =
    ( ap
      ( unfocus-at-finite-sequence n i)
      ( is-section-focus-at-finite-sequence n j
        ( focus-at-finite-sequence n i u))) ∙
    ( is-retraction-focus-at-finite-sequence n i u)

  is-equiv-swap-at-finite-sequence :
    (i j : Fin (succ-ℕ n)) → is-equiv (swap-at-finite-sequence {A = A} n i j)
  is-equiv-swap-at-finite-sequence i j =
    is-equiv-is-invertible
      ( swap-at-finite-sequence n j i)
      ( is-section-swap-at-finite-sequence i j)
      ( is-section-swap-at-finite-sequence j i)

module _
  {l : Level} {A : UU l} (n : ℕ) (i j : Fin (succ-ℕ n))
  where

  equiv-swap-at-finite-sequence :
    fin-sequence A (succ-ℕ n) ≃ fin-sequence A (succ-ℕ n)
  equiv-swap-at-finite-sequence =
    ( swap-at-finite-sequence n i j , is-equiv-swap-at-finite-sequence n i j)
```

### Any sequence `u` in a type determines a sequence of finite sequences `(i : Fin n) ↦ u i`

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  fin-sequence-sequence : (n : ℕ) → fin-sequence A n
  fin-sequence-sequence n i = u (nat-Fin n i)

  eq-fin-sequence-sequence :
    (n : ℕ) → fin-sequence-sequence (succ-ℕ n) (neg-one-Fin n) ＝ u n
  eq-fin-sequence-sequence n = refl

  eq-zero-fin-sequence-sequence :
    (n : ℕ) → fin-sequence-sequence (succ-ℕ n) (zero-Fin n) ＝ u 0
  eq-zero-fin-sequence-sequence n = ap u (is-zero-nat-zero-Fin {n})

  eq-skip-zero-fin-sequence-sequence :
    (n : ℕ) (i : Fin n) →
    fin-sequence-sequence (succ-ℕ n) (skip-zero-Fin n i) ＝
    u (succ-ℕ (nat-Fin n i))
  eq-skip-zero-fin-sequence-sequence n i = ap u (nat-skip-zero-Fin n i)

module _
  {l : Level} {A : UU l} (u v : sequence A) (H : u ~ v)
  where

  htpy-fin-sequence-sequence :
    (n : ℕ) → fin-sequence-sequence u n ~ fin-sequence-sequence v n
  htpy-fin-sequence-sequence n i = H (nat-Fin n i)
```

## See also

- [Sequences](lists.sequences.md)
