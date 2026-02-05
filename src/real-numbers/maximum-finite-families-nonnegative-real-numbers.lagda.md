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
open import order-theory.joins-finite-families-join-semilattices

open import real-numbers.binary-maximum-nonnegative-real-numbers
open import real-numbers.nonnegative-real-numbers

open import univalent-combinatorics.inhabited-finite-types
```

</details>

## Idea

The
{{#concept "maximum" Disambiguation="inhabited finite family, nonnegative real numbers" Agda=max-finite-family-ℝ⁰⁺}}
of a family of
[nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) indexed by
an [inhabited finite type](univalent-combinatorics.inhabited-finite-types.md) is
their [least upper bound](order-theory.least-upper-bounds-large-posets.md).

## Definition

### The maximum of a nonempty finite sequence of nonnegative real numbers

```agda
module _
  {l : Level} (n : ℕ) (u : fin-sequence (ℝ⁰⁺ l) (succ-ℕ n))
  where

  max-fin-sequence-ℝ⁰⁺ : ℝ⁰⁺ l
  max-fin-sequence-ℝ⁰⁺ =
    join-fin-sequence-type-Order-Theoretic-Join-Semilattice
      ( ℝ⁰⁺-Order-Theoretic-Join-Semilattice l)
      ( n)
      ( u)
```

### The maximum of an inhabited finite family of nonnegative real numbers

```agda
module _
  {l1 l2 : Level} (I : Inhabited-Finite-Type l1)
  (f : type-Inhabited-Finite-Type I → ℝ⁰⁺ l2)
  where

  max-finite-family-ℝ⁰⁺ : ℝ⁰⁺ l2
  max-finite-family-ℝ⁰⁺ =
    join-inhabited-finite-family-Order-Theoretic-Join-Semilattice
      ( ℝ⁰⁺-Order-Theoretic-Join-Semilattice l2)
      ( I)
      ( f)
```
