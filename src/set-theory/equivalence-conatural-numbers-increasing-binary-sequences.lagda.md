# Equivalence of conatural numbers and increasing binary sequences

```agda
{-# OPTIONS --guardedness #-}

module set-theory.equivalence-conatural-numbers-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.conatural-numbers
open import elementary-number-theory.equality-conatural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.inequality-booleans
open import foundation.injective-maps
open import foundation.maybe
open import foundation.negated-equality
open import foundation.retractions
open import foundation.sections
open import foundation.unit-type

open import foundation-core.empty-types
open import foundation-core.identity-types

open import set-theory.inclusion-natural-numbers-increasing-binary-sequences
open import set-theory.increasing-binary-sequences
```

</details>

## Idea

The type of [conatural numbers](elementary-number-theory.conatural-numbers.md)
$ℕ_∞$, which is defined as the terminal coalgebra of the `Maybe` monad, is
[equivalent](foundation.equivalences.md) to the type of
[increasing binary sequences](set-theory.increasing-binary-sequences.md).

## Maps between the conatural numbers and increasing binary sequences

```agda
conatural-number-ℕ∞↗ : ℕ∞↗ → ℕ∞
conatural-number-ℕ∞↗ = coit-ℕ∞ decons-ℕ∞↗

sequence-increasing-binary-sequence-ℕ∞ : ℕ∞ → ℕ → bool
sequence-increasing-binary-sequence-ℕ∞ x zero-ℕ with decons-ℕ∞ x
... | inl _ = false
... | inr _ = true
sequence-increasing-binary-sequence-ℕ∞ x (succ-ℕ n) with decons-ℕ∞ x
... | inl y = sequence-increasing-binary-sequence-ℕ∞ y n
... | inr _ = true

is-increasing-sequence-increasing-binary-sequence-ℕ∞ :
  (x : ℕ∞) →
  is-increasing-binary-sequence (sequence-increasing-binary-sequence-ℕ∞ x)
is-increasing-sequence-increasing-binary-sequence-ℕ∞ x zero-ℕ
  with decons-ℕ∞ x
... | inl y = star
... | inr y = star
is-increasing-sequence-increasing-binary-sequence-ℕ∞ x (succ-ℕ n)
  with decons-ℕ∞ x
... | inl y = is-increasing-sequence-increasing-binary-sequence-ℕ∞ y n
... | inr y = star

increasing-binary-sequence-ℕ∞ : ℕ∞ → ℕ∞↗
increasing-binary-sequence-ℕ∞ x =
  ( sequence-increasing-binary-sequence-ℕ∞ x ,
    is-increasing-sequence-increasing-binary-sequence-ℕ∞ x)
```

## Basic computations

```agda
abstract
  compute-conatural-number-zero-ℕ∞↗ :
    conatural-number-ℕ∞↗ zero-ℕ∞↗ ＝ zero-ℕ∞
  compute-conatural-number-zero-ℕ∞↗ =
    is-injective-decons-ℕ∞ refl

  compute-conatural-number-ℕ∞↗-succ :
    (x : ℕ∞↗) →
    conatural-number-ℕ∞↗ (succ-ℕ∞↗ x) ＝
    succ-ℕ∞ (conatural-number-ℕ∞↗ x)
  compute-conatural-number-ℕ∞↗-succ x =
    is-injective-decons-ℕ∞ refl

  compute-decons-conatural-number-increasing-binary-sequence-ℕ∞ :
    (x : ℕ∞) →
    decons-ℕ∞ (conatural-number-ℕ∞↗ (increasing-binary-sequence-ℕ∞ x)) ＝
    map-Maybe conatural-number-ℕ∞↗
      ( decons-ℕ∞↗ (increasing-binary-sequence-ℕ∞ x))
  compute-decons-conatural-number-increasing-binary-sequence-ℕ∞ x
    with decons-ℕ∞ x
  ... | inl y = refl
  ... | inr y = refl

  compute-sequence-increasing-binary-sequence-zero-ℕ∞ :
    (x : ℕ∞) →
    sequence-increasing-binary-sequence-ℕ∞ x zero-ℕ ＝
    rec-coproduct (λ _ → false) (λ _ → true) (decons-ℕ∞ x)
  compute-sequence-increasing-binary-sequence-zero-ℕ∞ x with decons-ℕ∞ x
  ... | inl y = refl
  ... | inr y = refl

  compute-sequence-increasing-binary-sequence-ℕ∞-succ :
    (x : ℕ∞) (n : ℕ) →
    sequence-increasing-binary-sequence-ℕ∞ x (succ-ℕ n) ＝
    rec-coproduct
      ( λ y → sequence-increasing-binary-sequence-ℕ∞ y n)
      ( λ _ → true)
      ( decons-ℕ∞ x)
  compute-sequence-increasing-binary-sequence-ℕ∞-succ x n with decons-ℕ∞ x
  ... | inl y = refl
  ... | inr y = refl

  Eq-compute-increasing-binary-sequence-zero-ℕ∞ :
    Eq-ℕ∞↗ (increasing-binary-sequence-ℕ∞ zero-ℕ∞) zero-ℕ∞↗
  Eq-compute-increasing-binary-sequence-zero-ℕ∞ zero-ℕ = refl
  Eq-compute-increasing-binary-sequence-zero-ℕ∞ (succ-ℕ n) = refl

  compute-increasing-binary-sequence-zero-ℕ∞ :
    increasing-binary-sequence-ℕ∞ zero-ℕ∞ ＝ zero-ℕ∞↗
  compute-increasing-binary-sequence-zero-ℕ∞ =
    eq-Eq-ℕ∞↗ Eq-compute-increasing-binary-sequence-zero-ℕ∞

  Eq-compute-increasing-binary-sequence-succ-ℕ∞ :
    (x : ℕ∞) →
    Eq-ℕ∞↗
      ( increasing-binary-sequence-ℕ∞ (succ-ℕ∞ x))
      ( succ-ℕ∞↗ (increasing-binary-sequence-ℕ∞ x))
  Eq-compute-increasing-binary-sequence-succ-ℕ∞ x zero-ℕ = refl
  Eq-compute-increasing-binary-sequence-succ-ℕ∞ x (succ-ℕ n) = refl

  compute-increasing-binary-sequence-succ-ℕ∞ :
    (x : ℕ∞) →
    increasing-binary-sequence-ℕ∞ (succ-ℕ∞ x) ＝
    succ-ℕ∞↗ (increasing-binary-sequence-ℕ∞ x)
  compute-increasing-binary-sequence-succ-ℕ∞ x =
    eq-Eq-ℕ∞↗ (Eq-compute-increasing-binary-sequence-succ-ℕ∞ x)

  Eq-compute-increasing-binary-sequence-infinity-ℕ∞ :
    Eq-ℕ∞↗ (increasing-binary-sequence-ℕ∞ infinity-ℕ∞) infinity-ℕ∞↗
  Eq-compute-increasing-binary-sequence-infinity-ℕ∞ zero-ℕ = refl
  Eq-compute-increasing-binary-sequence-infinity-ℕ∞ (succ-ℕ n) =
    Eq-compute-increasing-binary-sequence-infinity-ℕ∞ n

  compute-increasing-binary-sequence-infinity-ℕ∞ :
    increasing-binary-sequence-ℕ∞ infinity-ℕ∞ ＝ infinity-ℕ∞↗
  compute-increasing-binary-sequence-infinity-ℕ∞ =
    eq-Eq-ℕ∞↗ Eq-compute-increasing-binary-sequence-infinity-ℕ∞
```

## `ℕ∞ → ℕ∞↗` is a retraction of `ℕ∞↗ → ℕ∞`

```agda
abstract
  eq-succ-is-unit-decons-conatural-number-ℕ∞↗ :
    (x : ℕ∞↗) (y : ℕ∞) →
    decons-ℕ∞ (conatural-number-ℕ∞↗ x) ＝ unit-Maybe y →
    conatural-number-ℕ∞↗ x ＝ succ-ℕ∞ y
  eq-succ-is-unit-decons-conatural-number-ℕ∞↗ x y =
    is-injective-decons-ℕ∞

  is-true-sequence-zero-is-exception-decons-conatural-number-ℕ∞↗ :
    (x : ℕ∞↗) →
    decons-ℕ∞ (conatural-number-ℕ∞↗ x) ＝ exception-Maybe →
    is-true (sequence-ℕ∞↗ x 0)
  is-true-sequence-zero-is-exception-decons-conatural-number-ℕ∞↗ x p
    with sequence-ℕ∞↗ x 0 in q
  ... | true = refl
  ... | false =
    ex-falso
      ( is-not-exception-unit-Maybe (conatural-number-ℕ∞↗ (shift-left-ℕ∞↗ x)) p)

  is-false-sequence-zero-is-unit-decons-conatural-number-ℕ∞↗ :
    (x : ℕ∞↗) (y : ℕ∞) →
    decons-ℕ∞ (conatural-number-ℕ∞↗ x) ＝ unit-Maybe y →
    is-false (sequence-ℕ∞↗ x 0)
  is-false-sequence-zero-is-unit-decons-conatural-number-ℕ∞↗ x y p
    with sequence-ℕ∞↗ x 0 in q
  ... | false = refl
  ... | true = ex-falso (is-not-exception-unit-Maybe y (inv p))

  eq-shift-left-conatural-number-ℕ∞↗ :
    (x : ℕ∞↗) (y : ℕ∞) →
    decons-ℕ∞ (conatural-number-ℕ∞↗ x) ＝ unit-Maybe y →
    is-false (sequence-ℕ∞↗ x 0) →
    y ＝ conatural-number-ℕ∞↗ (shift-left-ℕ∞↗ x)
  eq-shift-left-conatural-number-ℕ∞↗ x y p q =
    is-injective-succ-ℕ∞
      ( ( inv
          ( eq-succ-is-unit-decons-conatural-number-ℕ∞↗ x y p)) ∙
        ( ( ap conatural-number-ℕ∞↗ (eq-succ-shift-left-ℕ∞↗ x q)) ∙
          ( compute-conatural-number-ℕ∞↗-succ (shift-left-ℕ∞↗ x))))

  Eq-sequence-increasing-binary-sequence-conatural-number-ℕ∞↗ :
    (x : ℕ∞↗) →
    sequence-ℕ∞↗ (increasing-binary-sequence-ℕ∞ (conatural-number-ℕ∞↗ x)) ~
    sequence-ℕ∞↗ x
  Eq-sequence-increasing-binary-sequence-conatural-number-ℕ∞↗ x zero-ℕ
    with decons-ℕ∞ (conatural-number-ℕ∞↗ x) in r
  ... | inl y =
    inv
      ( is-false-sequence-zero-is-unit-decons-conatural-number-ℕ∞↗ x y r)
  ... | inr y =
    inv
      ( is-true-sequence-zero-is-exception-decons-conatural-number-ℕ∞↗ x r)
  Eq-sequence-increasing-binary-sequence-conatural-number-ℕ∞↗ x (succ-ℕ n)
    with decons-ℕ∞ (conatural-number-ℕ∞↗ x) in r
  ... | inl y =
    ( ap
      ( λ z → sequence-increasing-binary-sequence-ℕ∞ z n)
      ( eq-shift-left-conatural-number-ℕ∞↗ x y r
        ( is-false-sequence-zero-is-unit-decons-conatural-number-ℕ∞↗ x y r))) ∙
    ( Eq-sequence-increasing-binary-sequence-conatural-number-ℕ∞↗
      ( shift-left-ℕ∞↗ x)
      ( n))
  ... | inr y =
    inv
      ( Eq-zero-is-zero-ℕ∞↗
        ( x)
        ( is-true-sequence-zero-is-exception-decons-conatural-number-ℕ∞↗ x r)
        ( succ-ℕ n))

  is-retraction-increasing-binary-sequence-ℕ∞ :
    is-retraction conatural-number-ℕ∞↗ increasing-binary-sequence-ℕ∞
  is-retraction-increasing-binary-sequence-ℕ∞ x =
    eq-Eq-ℕ∞↗ (Eq-sequence-increasing-binary-sequence-conatural-number-ℕ∞↗ x)
```

## `ℕ∞ → ℕ∞↗` is a section of `ℕ∞↗ → ℕ∞`

```agda
abstract
  eq-shift-left-increasing-binary-sequence-ℕ∞ :
    (x y : ℕ∞) →
    decons-ℕ∞ x ＝ unit-Maybe y →
    shift-left-ℕ∞↗ (increasing-binary-sequence-ℕ∞ x) ＝
    increasing-binary-sequence-ℕ∞ y
  eq-shift-left-increasing-binary-sequence-ℕ∞ x y p =
    ( ap
      ( shift-left-ℕ∞↗)
      ( ( ap increasing-binary-sequence-ℕ∞
          ( is-injective-decons-ℕ∞ {x} {succ-ℕ∞ y} p)) ∙
        ( compute-increasing-binary-sequence-succ-ℕ∞ y)))

  Eq-Eq-increasing-binary-sequence-ℕ∞ :
    {x y : ℕ∞} →
    Eq-ℕ∞↗ (increasing-binary-sequence-ℕ∞ x) (increasing-binary-sequence-ℕ∞ y) →
    Eq-ℕ∞ x y
  decons-Eq-ℕ∞
    ( Eq-Eq-increasing-binary-sequence-ℕ∞ {x} {y} p)
    with decons-ℕ∞ x in rx | decons-ℕ∞ y in ry | p zero-ℕ
  ... | inl x' | inl y' | p0 =
    cons-Eq-Maybe-ℕ∞
      ( Eq-Eq-increasing-binary-sequence-ℕ∞
        ( Eq-eq-ℕ∞↗
          ( ( inv (eq-shift-left-increasing-binary-sequence-ℕ∞ x x' rx)) ∙
            ( eq-Eq-ℕ∞↗ (p ∘ succ-ℕ)) ∙
            ( eq-shift-left-increasing-binary-sequence-ℕ∞ y y' ry))))
  ... | inl x' | inr y' | ()
  ... | inr x' | inl y' | ()
  ... | inr x' | inr y' | p0 = cons-Eq-Maybe-ℕ∞ star

  is-injective-increasing-binary-sequence-ℕ∞ :
    is-injective increasing-binary-sequence-ℕ∞
  is-injective-increasing-binary-sequence-ℕ∞ p =
    eq-Eq-ℕ∞ (Eq-Eq-increasing-binary-sequence-ℕ∞ (Eq-eq-ℕ∞↗ p))

  is-section-increasing-binary-sequence-ℕ∞ :
    is-section conatural-number-ℕ∞↗ increasing-binary-sequence-ℕ∞
  is-section-increasing-binary-sequence-ℕ∞ x =
    is-injective-increasing-binary-sequence-ℕ∞
      ( is-retraction-increasing-binary-sequence-ℕ∞
        ( increasing-binary-sequence-ℕ∞ x))
```

## Compatibility with the inclusion of the natural numbers

```agda
abstract
  neq-in-image-increasing-binary-sequence-ℕ-increasing-binary-sequence-ℕ∞-infinity :
    (n : ℕ) →
    increasing-binary-sequence-ℕ∞ infinity-ℕ∞ ≠ increasing-binary-sequence-ℕ n
  neq-in-image-increasing-binary-sequence-ℕ-increasing-binary-sequence-ℕ∞-infinity
    n p =
    neq-infinity-increasing-binary-sequence-ℕ n
      ( inv p ∙ compute-increasing-binary-sequence-infinity-ℕ∞)

  compute-conatural-number-infinity-ℕ∞↗ :
    conatural-number-ℕ∞↗ infinity-ℕ∞↗ ＝ infinity-ℕ∞
  compute-conatural-number-infinity-ℕ∞↗ =
    ( ap
      ( conatural-number-ℕ∞↗)
      ( inv compute-increasing-binary-sequence-infinity-ℕ∞)) ∙
    ( is-section-increasing-binary-sequence-ℕ∞ infinity-ℕ∞)
```

## Equivalence

```agda
is-equiv-conatural-number-ℕ∞↗ :
  is-equiv conatural-number-ℕ∞↗
is-equiv-conatural-number-ℕ∞↗ =
  is-equiv-is-invertible
    increasing-binary-sequence-ℕ∞
    is-section-increasing-binary-sequence-ℕ∞
    is-retraction-increasing-binary-sequence-ℕ∞

equiv-conatural-number-ℕ∞↗ : ℕ∞↗ ≃ ℕ∞
equiv-conatural-number-ℕ∞↗ =
  ( conatural-number-ℕ∞↗ , is-equiv-conatural-number-ℕ∞↗)

is-equiv-increasing-binary-sequence-ℕ∞ :
  is-equiv increasing-binary-sequence-ℕ∞
is-equiv-increasing-binary-sequence-ℕ∞ =
  is-equiv-is-invertible
    conatural-number-ℕ∞↗
    is-retraction-increasing-binary-sequence-ℕ∞
    is-section-increasing-binary-sequence-ℕ∞

equiv-increasing-binary-sequence-ℕ∞ : ℕ∞ ≃ ℕ∞↗
equiv-increasing-binary-sequence-ℕ∞ =
  ( increasing-binary-sequence-ℕ∞ ,
    is-equiv-increasing-binary-sequence-ℕ∞)
```
