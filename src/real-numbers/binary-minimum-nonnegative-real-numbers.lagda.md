# The binary minimum of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.binary-minimum-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-meet-semilattices
open import order-theory.meet-semilattices

open import real-numbers.binary-minimum-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

The
{{#concept "minimum" Disambiguation="binary, nonnegative real numbers" Agda=min-ℝ⁰⁺}}
of two [nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) is
nonnegative.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x⁰⁺@(x , 0≤x) : ℝ⁰⁺ l1)
  (y⁰⁺@(y , 0≤y) : ℝ⁰⁺ l2)
  where

  abstract
    is-nonnegative-min-real-ℝ⁰⁺ : is-nonnegative-ℝ (min-ℝ x y)
    is-nonnegative-min-real-ℝ⁰⁺ = leq-min-leq-leq-ℝ x y zero-ℝ 0≤x 0≤y

  min-ℝ⁰⁺ : ℝ⁰⁺ (l1 ⊔ l2)
  min-ℝ⁰⁺ = (min-ℝ x y , is-nonnegative-min-real-ℝ⁰⁺)
```

## Properties

### The binary minimum is a greatest lower bound

```agda
module _
  {l1 l2 : Level}
  (x⁰⁺@(x , 0≤x) : ℝ⁰⁺ l1)
  (y⁰⁺@(y , 0≤y) : ℝ⁰⁺ l2)
  where

  abstract
    is-greatest-binary-lower-bound-min-ℝ⁰⁺ :
      is-greatest-binary-lower-bound-Large-Poset
        ( ℝ⁰⁺-Large-Poset)
        ( x⁰⁺)
        ( y⁰⁺)
        ( min-ℝ⁰⁺ x⁰⁺ y⁰⁺)
    is-greatest-binary-lower-bound-min-ℝ⁰⁺ (z , _) =
      is-greatest-binary-lower-bound-min-ℝ x y z
```

### The large poset of nonnegative real numbers has meets

```agda
has-meets-large-poset-ℝ⁰⁺ : has-meets-Large-Poset ℝ⁰⁺-Large-Poset
has-meets-ℝ⁰⁺-Large-Poset =
  λ where
    .meet-has-meets-Large-Poset → min-ℝ⁰⁺
    .is-greatest-binary-lower-bound-meet-has-meets-Large-Poset →
      is-greatest-binary-lower-bound-min-ℝ⁰⁺
```

### The nonnegative real numbers at a universe level form a meet-semilattice

```agda
order-theoretic-meet-semiliattice-ℝ⁰⁺ :
  (l : Level) → Order-Theoretic-Meet-Semilattice (lsuc l) l
pr1 (ℝ⁰⁺-Order-Theoretic-Meet-Semilattice l) = ℝ⁰⁺-Poset l
pr2 (ℝ⁰⁺-Order-Theoretic-Meet-Semilattice l) x y =
  ( min-ℝ⁰⁺ x y , is-greatest-binary-lower-bound-min-ℝ⁰⁺ x y)
```

## See also

- [The binary minimum of real numbers](real-numbers.binary-minimum-real-numbers.md)
