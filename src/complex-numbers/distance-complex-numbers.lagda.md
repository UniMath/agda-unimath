# The distance between complex numbers

```agda
{-# OPTIONS --lossy-unification #-}

module complex-numbers.distance-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.addition-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.difference-complex-numbers
open import complex-numbers.magnitude-complex-numbers
open import complex-numbers.similarity-complex-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.zero-real-numbers
```

</details>

## Idea

The
{{#concept "distance" Disambiguation="between two complex numbers" Agda=dist-ℂ}}
between two [complex numbers](complex-numbers.complex-numbers.md) is the
[magnitude](complex-numbers.magnitude-complex-numbers.md) of their
[difference](complex-numbers.difference-complex-numbers.md).

## Definition

```agda
nonnegative-dist-ℂ : {l1 l2 : Level} → ℂ l1 → ℂ l2 → ℝ⁰⁺ (l1 ⊔ l2)
nonnegative-dist-ℂ z w = nonnegative-magnitude-ℂ (z -ℂ w)

dist-ℂ : {l1 l2 : Level} → ℂ l1 → ℂ l2 → ℝ (l1 ⊔ l2)
dist-ℂ z w = magnitude-ℂ (z -ℂ w)
```

## Properties

### The distance function in `ℂ` is reflexive

```agda
abstract
  refl-dist-ℂ :
    {l : Level} (z : ℂ l) → is-zero-ℝ (dist-ℂ z z)
  refl-dist-ℂ z =
    transitive-sim-ℝ _ _ _
      ( sim-eq-ℝ magnitude-zero-ℂ)
      ( preserves-sim-magnitude-ℂ (right-inverse-law-add-ℂ z))
```

### The distance function in `ℂ` is symmetric

```agda
abstract
  symmetric-dist-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) → dist-ℂ z w ＝ dist-ℂ w z
  symmetric-dist-ℂ z w =
    ( inv (magnitude-neg-ℂ (z -ℂ w))) ∙
    ( ap magnitude-ℂ (distributive-neg-diff-ℂ z w))
```

### The distance function in `ℂ` is triangular

```agda
abstract
  triangular-dist-ℂ :
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    leq-ℝ (dist-ℂ x z) (dist-ℂ x y +ℝ dist-ℂ y z)
  triangular-dist-ℂ x y z =
    preserves-leq-left-sim-ℝ
      ( preserves-sim-magnitude-ℂ (add-diff-ℂ x y z))
      ( triangular-magnitude-ℂ (x -ℂ y) (y -ℂ z))
```

### The distance function in `ℂ` is extensional

```agda
abstract
  is-extensional-dist-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) → is-zero-ℝ (dist-ℂ z w) → sim-ℂ z w
  is-extensional-dist-ℂ z w |z-w|=0 =
    sim-is-zero-diff-ℂ z w (is-extensional-magnitude-ℂ (z -ℂ w) |z-w|=0)
```
