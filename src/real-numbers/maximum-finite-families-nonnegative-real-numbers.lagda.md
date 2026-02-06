# The maximum of finite families of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.maximum-finite-families-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import lists.finite-sequences

open import order-theory.join-semilattices
open import order-theory.joins-finite-families-large-join-semilattices
open import order-theory.least-upper-bounds-large-posets

open import real-numbers.binary-maximum-nonnegative-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.nonnegative-real-numbers

open import univalent-combinatorics.finite-types
```

</details>

## Idea

The
{{#concept "maximum" Disambiguation="inhabited finite family, nonnegative real numbers" Agda=max-finite-family-ℝ⁰⁺}}
of a family of
[nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) indexed by
a [finite type](univalent-combinatorics.finite-types.md) is their
[least upper bound](order-theory.least-upper-bounds-large-posets.md).

## Definition

### The maximum of a finite sequence of nonnegative real numbers

```agda
module _
  {l : Level} (n : ℕ) (u : fin-sequence (ℝ⁰⁺ l) n)
  where

  max-fin-sequence-ℝ⁰⁺ : ℝ⁰⁺ l
  max-fin-sequence-ℝ⁰⁺ =
    join-fin-sequence-type-Large-Join-Semilattice ℝ⁰⁺-Large-Join-Semilattice n u
```

### The maximum of an finite family of nonnegative real numbers

```agda
module _
  {l1 l2 : Level} (I : Finite-Type l1)
  (f : type-Finite-Type I → ℝ⁰⁺ l2)
  where

  max-finite-family-ℝ⁰⁺ : ℝ⁰⁺ l2
  max-finite-family-ℝ⁰⁺ =
    join-finite-family-type-Large-Join-Semilattice
      ( ℝ⁰⁺-Large-Join-Semilattice)
      ( I)
      ( f)
```

## Properties

### The maximum of a finite sequence of nonnegative real numbers is its least upper bound

```agda
module _
  {l : Level} (n : ℕ) (u : fin-sequence (ℝ⁰⁺ l) n)
  where

  abstract
    is-least-upper-bound-max-fin-sequence-ℝ⁰⁺ :
      is-least-upper-bound-family-of-elements-Large-Poset
        ( ℝ⁰⁺-Large-Poset)
        ( u)
        ( max-fin-sequence-ℝ⁰⁺ n u)
    is-least-upper-bound-max-fin-sequence-ℝ⁰⁺ =
      is-least-upper-bound-join-fin-sequence-type-Large-Join-Semilattice
        ( ℝ⁰⁺-Large-Join-Semilattice)
        ( n)
        ( u)
```

### The maximum of a finite family of nonnegative real numbers is its least upper bound

```agda
module _
  {l1 l2 : Level} (I : Finite-Type l1)
  (f : type-Finite-Type I → ℝ⁰⁺ l2)
  where

  abstract
    is-least-upper-bound-max-finite-family-ℝ⁰⁺ :
      is-least-upper-bound-family-of-elements-Large-Poset
        ( ℝ⁰⁺-Large-Poset)
        ( f)
        ( max-finite-family-ℝ⁰⁺ I f)
    is-least-upper-bound-max-finite-family-ℝ⁰⁺ =
      is-least-upper-bound-join-finite-family-type-Large-Join-Semilattice
        ( ℝ⁰⁺-Large-Join-Semilattice)
        ( I)
        ( f)
```
