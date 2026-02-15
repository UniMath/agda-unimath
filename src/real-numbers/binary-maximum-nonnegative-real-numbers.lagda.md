# The binary maximum of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.binary-maximum-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.universe-levels

open import order-theory.join-semilattices
open import order-theory.large-join-semilattices
open import order-theory.least-upper-bounds-large-posets

open import real-numbers.binary-maximum-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

The
{{#concept "maximum" Disambiguation="binary, nonnegative real numbers" Agda=max-ℝ⁰⁺}}
of two [nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) is
itself nonnegative.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x⁰⁺@(x , 0≤x) : ℝ⁰⁺ l1)
  (y⁰⁺@(y , 0≤y) : ℝ⁰⁺ l2)
  where

  abstract
    is-nonnegative-max-real-ℝ⁰⁺ : is-nonnegative-ℝ (max-ℝ x y)
    is-nonnegative-max-real-ℝ⁰⁺ =
      transitive-leq-ℝ zero-ℝ x (max-ℝ x y) (leq-left-max-ℝ x y) 0≤x

  max-ℝ⁰⁺ : ℝ⁰⁺ (l1 ⊔ l2)
  max-ℝ⁰⁺ = (max-ℝ x y , is-nonnegative-max-real-ℝ⁰⁺)
```

## Properties

### The binary maximum of nonnegative real numbers is a least upper bound

```agda
module _
  {l1 l2 : Level}
  (x⁰⁺@(x , 0≤x) : ℝ⁰⁺ l1)
  (y⁰⁺@(y , 0≤y) : ℝ⁰⁺ l2)
  where

  abstract
    is-least-binary-upper-bound-max-ℝ⁰⁺ :
      is-least-binary-upper-bound-Large-Poset
        ( ℝ⁰⁺-Large-Poset)
        ( x⁰⁺)
        ( y⁰⁺)
        ( max-ℝ⁰⁺ x⁰⁺ y⁰⁺)
    is-least-binary-upper-bound-max-ℝ⁰⁺ (z , _) =
      is-least-binary-upper-bound-max-ℝ x y z
```

### The large poset of nonnegative real numbers has joins

```agda
has-joins-large-poset-ℝ⁰⁺ : has-joins-Large-Poset ℝ⁰⁺-Large-Poset
has-joins-ℝ⁰⁺-Large-Poset =
  λ where
    .join-has-joins-Large-Poset →
      max-ℝ⁰⁺
    .is-least-binary-upper-bound-join-has-joins-Large-Poset →
      is-least-binary-upper-bound-max-ℝ⁰⁺
```

### The nonnegative real numbers are a large join semilattice

```agda
is-large-join-semilattice-large-poset-ℝ⁰⁺ :
  is-large-join-semilattice-Large-Poset ℝ⁰⁺-Large-Poset
is-large-join-semilattice-ℝ⁰⁺-Large-Poset =
  λ where
    .has-joins-is-large-join-semilattice-Large-Poset →
      has-joins-ℝ⁰⁺-Large-Poset
    .has-bottom-element-is-large-join-semilattice-Large-Poset →
      has-bottom-element-ℝ⁰⁺-Large-Poset

large-join-semilattice-ℝ⁰⁺ : Large-Join-Semilattice lsuc (_⊔_)
ℝ⁰⁺-Large-Join-Semilattice =
  λ where
    .large-poset-Large-Join-Semilattice → ℝ⁰⁺-Large-Poset
    .is-large-join-semilattice-Large-Join-Semilattice →
      is-large-join-semilattice-ℝ⁰⁺-Large-Poset

order-theoretic-join-semilattice-ℝ⁰⁺ :
  (l : Level) → Order-Theoretic-Join-Semilattice (lsuc l) l
ℝ⁰⁺-Order-Theoretic-Join-Semilattice =
  order-theoretic-join-semilattice-Large-Join-Semilattice
    ( ℝ⁰⁺-Large-Join-Semilattice)
```

## See also

- [The binary maximum of real numbers](real-numbers.binary-maximum-real-numbers.md)
