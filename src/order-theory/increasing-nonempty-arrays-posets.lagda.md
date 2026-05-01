# Increasing nonempty arrays in posets

```agda
module order-theory.increasing-nonempty-arrays-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import lists.arrays
open import lists.finite-sequences
open import lists.nonempty-arrays

open import order-theory.increasing-arrays-posets
open import order-theory.increasing-finite-sequences-posets
open import order-theory.opposite-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A [nonempty array](lists.nonempty-arrays.md) in a
[poset](order-theory.posets.md) is
{{#concept "increasing" Disambiguation="nonempty array in a poset" Agda=is-increasing-nonempty-array-type-Poset}}
if its associated [finite sequence](lists.finite-sequences.md) is
[increasing](order-theory.increasing-finite-sequences-posets.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  is-increasing-prop-nonempty-array-type-Poset :
    subtype l2 (nonempty-array (type-Poset P))
  is-increasing-prop-nonempty-array-type-Poset (u , _) =
    is-increasing-prop-array-type-Poset P u

  is-increasing-nonempty-array-type-Poset :
    nonempty-array (type-Poset P) → UU l2
  is-increasing-nonempty-array-type-Poset =
    is-in-subtype is-increasing-prop-nonempty-array-type-Poset

  increasing-nonempty-array-type-Poset : UU (l1 ⊔ l2)
  increasing-nonempty-array-type-Poset =
    type-subtype is-increasing-prop-nonempty-array-type-Poset

module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  nonempty-array-increasing-nonempty-array-type-Poset :
    increasing-nonempty-array-type-Poset P → nonempty-array (type-Poset P)
  nonempty-array-increasing-nonempty-array-type-Poset = pr1

  is-increasing-nonempty-array-increasing-nonempty-array-type-Poset :
    (u : increasing-nonempty-array-type-Poset P) →
    is-increasing-nonempty-array-type-Poset
      ( P)
      ( nonempty-array-increasing-nonempty-array-type-Poset u)
  is-increasing-nonempty-array-increasing-nonempty-array-type-Poset = pr2

  array-increasing-nonempty-array-type-Poset :
    increasing-nonempty-array-type-Poset P → array (type-Poset P)
  array-increasing-nonempty-array-type-Poset ((u , _) , _) = u

  length-increasing-nonempty-array-type-Poset :
    increasing-nonempty-array-type-Poset P → ℕ
  length-increasing-nonempty-array-type-Poset (((n , _) , _) , _) = n

  head-increasing-nonempty-array-type-Poset :
    increasing-nonempty-array-type-Poset P → type-Poset P
  head-increasing-nonempty-array-type-Poset =
    head-nonempty-array ∘ nonempty-array-increasing-nonempty-array-type-Poset

  last-increasing-nonempty-array-type-Poset :
    increasing-nonempty-array-type-Poset P → type-Poset P
  last-increasing-nonempty-array-type-Poset =
    last-nonempty-array ∘ nonempty-array-increasing-nonempty-array-type-Poset

  fin-sequence-increasing-nonempty-array-type-Poset :
    (u : increasing-nonempty-array-type-Poset P) →
    fin-sequence (type-Poset P) (length-increasing-nonempty-array-type-Poset u)
  fin-sequence-increasing-nonempty-array-type-Poset (((_ , u) , _) , _) = u
```

## Properties

### The tail of an increasing nonempty array is increasing

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  array-tail-increasing-nonempty-array-type-Poset :
    increasing-nonempty-array-type-Poset P → array (type-Poset P)
  array-tail-increasing-nonempty-array-type-Poset (u , _) =
    tail-nonempty-array u

  abstract
    is-increasing-array-tail-increasing-nonempty-array-type-Poset :
      (u : increasing-nonempty-array-type-Poset P) →
      is-increasing-array-type-Poset
        ( P)
        ( array-tail-increasing-nonempty-array-type-Poset u)
    is-increasing-array-tail-increasing-nonempty-array-type-Poset
      (((succ-ℕ n , u) , _) , H) i j =
      H (inl-Fin n i) (inl-Fin n j)

  tail-increasing-nonempty-array-type-Poset :
    increasing-nonempty-array-type-Poset P → increasing-array-type-Poset P
  tail-increasing-nonempty-array-type-Poset
    uu@(((succ-ℕ n , u) , _) , is-increasing-u) =
    ( (n , tail-fin-sequence n u) ,
      is-increasing-array-tail-increasing-nonempty-array-type-Poset uu)
```

### The initial segment of an increasing nonempty array is increasing

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  array-init-increasing-nonempty-array-type-Poset :
    increasing-nonempty-array-type-Poset P → array (type-Poset P)
  array-init-increasing-nonempty-array-type-Poset (u , _) =
    init-nonempty-array u

  abstract
    is-increasing-array-init-increasing-nonempty-array-type-Poset :
      (u : increasing-nonempty-array-type-Poset P) →
      is-increasing-array-type-Poset
        ( P)
        ( array-init-increasing-nonempty-array-type-Poset u)
    is-increasing-array-init-increasing-nonempty-array-type-Poset
      (((succ-ℕ n , u) , _) , H) =
      preserves-order-comp-Poset
        ( Fin-Poset n)
        ( Fin-Poset (succ-ℕ n))
        ( P)
        ( u , H)
        ( inr-Fin n , preserves-order-inr-Fin n)

  init-increasing-nonempty-array-type-Poset :
    increasing-nonempty-array-type-Poset P → increasing-array-type-Poset P
  init-increasing-nonempty-array-type-Poset u =
    ( array-init-increasing-nonempty-array-type-Poset u ,
      is-increasing-array-init-increasing-nonempty-array-type-Poset u)
```

### The head of a nonempty array is its greatest element

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  abstract
    is-greatest-element-head-increasing-nonempty-array-type-Poset :
      (u : increasing-nonempty-array-type-Poset P)
      (i : Fin (length-increasing-nonempty-array-type-Poset P u)) →
      leq-Poset P
        ( fin-sequence-increasing-nonempty-array-type-Poset P u i)
        ( head-increasing-nonempty-array-type-Poset P u)
    is-greatest-element-head-increasing-nonempty-array-type-Poset
      (((succ-ℕ n , u) , _) , H) i =
      H i (neg-one-Fin n) star
```

### The last element of a nonempty array is its least element

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  abstract
    is-least-element-last-increasing-nonempty-array-type-Poset :
      (u : increasing-nonempty-array-type-Poset P)
      (i : Fin (length-increasing-nonempty-array-type-Poset P u)) →
      leq-Poset P
        ( last-increasing-nonempty-array-type-Poset P u)
        ( fin-sequence-increasing-nonempty-array-type-Poset P u i)
    is-least-element-last-increasing-nonempty-array-type-Poset
      (((succ-ℕ n , u) , _) , H) i =
      H (zero-Fin n) i (leq-zero-Fin n i)
```
