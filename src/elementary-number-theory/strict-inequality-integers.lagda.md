# Strict inequality on the integers

```agda
module elementary-number-theory.strict-inequality-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-positive-and-negative-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.negative-integers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonpositive-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

An [integer](elementary-number-theory.integers.md) `x` is _strictly less than_
the integer `y` if the
[difference](elementary-number-theory.difference-integers.md) `y - x` is
[positive](elementary-number-theory.positive-integers.md). This relation defines
the {{#concept "standard strict ordering" Disambiguation="integers" Agda=le-ℤ}}
on the integers.

## Definition

### Strict inequality on the integers

```agda
le-prop-ℤ : ℤ → ℤ → Prop lzero
le-prop-ℤ x y = subtype-positive-ℤ (y -ℤ x)

le-ℤ : ℤ → ℤ → UU lzero
le-ℤ x y = type-Prop (le-prop-ℤ x y)

abstract
  is-prop-le-ℤ : (x y : ℤ) → is-prop (le-ℤ x y)
  is-prop-le-ℤ x y = is-prop-type-Prop (le-prop-ℤ x y)
```

## Properties

### Strict inequality on the integers implies inequality

```agda
abstract
  leq-le-ℤ : {x y : ℤ} → le-ℤ x y → leq-ℤ x y
  leq-le-ℤ {x} {y} = is-nonnegative-is-positive-ℤ
```

### Strict inequality on the integers is decidable

```agda
is-decidable-le-ℤ : (x y : ℤ) → (le-ℤ x y) + ¬ (le-ℤ x y)
is-decidable-le-ℤ x y = is-decidable-is-positive-ℤ (y -ℤ x)

le-ℤ-Decidable-Prop : (x y : ℤ) → Decidable-Prop lzero
le-ℤ-Decidable-Prop x y =
  ( le-ℤ x y ,
    is-prop-le-ℤ x y ,
    is-decidable-le-ℤ x y)
```

### Strict inequality on the integers is transitive

```agda
abstract
  transitive-le-ℤ : (k l m : ℤ) → le-ℤ l m → le-ℤ k l → le-ℤ k m
  transitive-le-ℤ k l m H K =
    is-positive-eq-ℤ
      ( triangle-diff-ℤ m l k)
      ( is-positive-add-ℤ H K)
```

### Strict inequality on the integers is asymmetric

```agda
abstract
  asymmetric-le-ℤ : (x y : ℤ) → le-ℤ x y → ¬ (le-ℤ y x)
  asymmetric-le-ℤ x y p =
    is-not-positive-is-nonpositive-ℤ
      ( is-nonpositive-eq-ℤ
        ( distributive-neg-diff-ℤ y x)
        ( is-nonpositive-neg-is-nonnegative-ℤ
          ( is-nonnegative-is-positive-ℤ p)))
```

### Strict inequality on the integers is connected

```agda
connected-le-ℤ : (x y : ℤ) → x ≠ y → le-ℤ x y + le-ℤ y x
connected-le-ℤ x y H =
  map-coproduct
    ( λ K →
      is-positive-eq-ℤ
        ( distributive-neg-diff-ℤ x y)
        ( is-positive-neg-is-negative-ℤ K))
    ( id)
    ( decide-sign-nonzero-ℤ (H ∘ eq-diff-ℤ))
```

### Any integer is strictly greater than its predecessor

```agda
abstract
  le-pred-ℤ : (x : ℤ) → le-ℤ (pred-ℤ x) x
  le-pred-ℤ x =
    is-positive-eq-ℤ
      ( inv (right-predecessor-law-diff-ℤ x x ∙ ap succ-ℤ (is-zero-diff-ℤ' x)))
      ( is-positive-int-positive-ℤ one-positive-ℤ)
```

### Any integer is strictly lesser than its successor

```agda
abstract
  le-succ-ℤ : (x : ℤ) → le-ℤ x (succ-ℤ x)
  le-succ-ℤ x =
    is-positive-eq-ℤ
      ( inv (left-successor-law-diff-ℤ x x ∙ ap succ-ℤ (is-zero-diff-ℤ' x)))
      ( is-positive-int-positive-ℤ one-positive-ℤ)
```

### Strict inequality on the integers is invariant by translation

```agda
module _
  (z x y : ℤ)
  where

  eq-translate-left-le-ℤ : le-ℤ (z +ℤ x) (z +ℤ y) ＝ le-ℤ x y
  eq-translate-left-le-ℤ = ap is-positive-ℤ (left-translation-diff-ℤ y x z)

  eq-translate-right-le-ℤ : le-ℤ (x +ℤ z) (y +ℤ z) ＝ le-ℤ x y
  eq-translate-right-le-ℤ = ap is-positive-ℤ (right-translation-diff-ℤ y x z)
```

### Addition on the integers preserves strict inequality

```agda
abstract
  preserves-le-left-add-ℤ :
    (z x y : ℤ) → le-ℤ x y → le-ℤ (x +ℤ z) (y +ℤ z)
  preserves-le-left-add-ℤ z x y =
    is-positive-eq-ℤ (inv (right-translation-diff-ℤ y x z))

  preserves-le-right-add-ℤ :
    (z x y : ℤ) → le-ℤ x y → le-ℤ (z +ℤ x) (z +ℤ y)
  preserves-le-right-add-ℤ z x y =
    is-positive-eq-ℤ (inv (left-translation-diff-ℤ y x z))

  preserves-le-add-ℤ :
    {a b c d : ℤ} → le-ℤ a b → le-ℤ c d → le-ℤ (a +ℤ c) (b +ℤ d)
  preserves-le-add-ℤ {a} {b} {c} {d} H K =
    transitive-le-ℤ
      ( a +ℤ c)
      ( b +ℤ c)
      ( b +ℤ d)
      ( preserves-le-right-add-ℤ b c d K)
      ( preserves-le-left-add-ℤ c a b H)
```

### Addition on the integers reflects strict inequality

```agda
abstract
  reflects-le-left-add-ℤ :
    (z x y : ℤ) → le-ℤ (x +ℤ z) (y +ℤ z) → le-ℤ x y
  reflects-le-left-add-ℤ z x y =
    is-positive-eq-ℤ (right-translation-diff-ℤ y x z)

  reflects-le-right-add-ℤ :
    (z x y : ℤ) → le-ℤ (z +ℤ x) (z +ℤ y) → le-ℤ x y
  reflects-le-right-add-ℤ z x y =
    is-positive-eq-ℤ (left-translation-diff-ℤ y x z)
```

### An integer `x` is positive if and only if `0 < x`

```agda
module _
  (x : ℤ)
  where

  abstract
    le-zero-is-positive-ℤ : is-positive-ℤ x → le-ℤ zero-ℤ x
    le-zero-is-positive-ℤ = is-positive-eq-ℤ (inv (right-zero-law-diff-ℤ x))

    is-positive-le-zero-ℤ : le-ℤ zero-ℤ x → is-positive-ℤ x
    is-positive-le-zero-ℤ = is-positive-eq-ℤ (right-zero-law-diff-ℤ x)

    eq-le-zero-is-positive-ℤ : is-positive-ℤ x ＝ le-ℤ zero-ℤ x
    eq-le-zero-is-positive-ℤ = ap is-positive-ℤ (inv (right-zero-law-diff-ℤ x))
```

### If an integer is greater than a positive integer it is positive

```agda
module _
  (x y : ℤ) (I : le-ℤ x y)
  where

  abstract
    is-positive-le-positive-ℤ : is-positive-ℤ x → is-positive-ℤ y
    is-positive-le-positive-ℤ H =
      is-positive-le-zero-ℤ y
        ( transitive-le-ℤ
          ( zero-ℤ)
          ( x)
          ( y)
          ( I)
          ( le-zero-is-positive-ℤ x H))
```

### An integer `x` is negative if and only if `x < 0`

```agda
module _
  (x : ℤ)
  where

  abstract
    le-zero-is-negative-ℤ : is-negative-ℤ x → le-ℤ x zero-ℤ
    le-zero-is-negative-ℤ = is-positive-neg-is-negative-ℤ

    is-negative-le-zero-ℤ : le-ℤ x zero-ℤ → is-negative-ℤ x
    is-negative-le-zero-ℤ H =
      is-negative-eq-ℤ
        ( neg-neg-ℤ x)
        ( is-negative-neg-is-positive-ℤ H)
```

### If an integer is lesser than a negative integer it is negative

```agda
module _
  (x y : ℤ) (I : le-ℤ x y)
  where
  abstract
    is-negative-le-negative-ℤ : is-negative-ℤ y → is-negative-ℤ x
    is-negative-le-negative-ℤ H =
      is-negative-le-zero-ℤ x
        ( transitive-le-ℤ
          ( x)
          ( y)
          ( zero-ℤ)
          ( le-zero-is-negative-ℤ y H)
          ( I))
```

### The inclusion of natural numbers preserves and reflects strict inequality

```agda
abstract
  preserves-le-int-ℕ : (m n : ℕ) → le-ℕ m n → le-ℤ (int-ℕ m) (int-ℕ n)
  preserves-le-int-ℕ zero-ℕ (succ-ℕ n) star =
    le-zero-is-positive-ℤ
      (int-ℕ (succ-ℕ n))
      (is-positive-int-is-nonzero-ℕ (succ-ℕ n) λ ())
  preserves-le-int-ℕ (succ-ℕ m) (succ-ℕ n) m<n =
    binary-tr
      ( le-ℤ)
      ( succ-int-ℕ m)
      ( succ-int-ℕ n)
      ( preserves-le-right-add-ℤ
        ( one-ℤ)
        ( int-ℕ m)
        ( int-ℕ n)
        ( preserves-le-int-ℕ m n m<n))

  reflects-le-int-ℕ : (m n : ℕ) → le-ℤ (int-ℕ m) (int-ℕ n) → le-ℕ m n
  reflects-le-int-ℕ zero-ℕ (succ-ℕ _) _ = star
  reflects-le-int-ℕ (succ-ℕ m) (succ-ℕ n) H =
    reflects-le-int-ℕ
      ( m)
      ( n)
      ( reflects-le-left-add-ℤ
        ( one-ℤ)
        ( int-ℕ m)
        ( int-ℕ n)
        ( binary-tr
          ( le-ℤ)
          ( inv (succ-int-ℕ m) ∙ is-right-add-one-succ-ℤ (int-ℕ m))
          ( inv (succ-int-ℕ n) ∙ is-right-add-one-succ-ℤ (int-ℕ n))
          ( H)))

  iff-le-int-ℕ : (m n : ℕ) → le-ℕ m n ↔ le-ℤ (int-ℕ m) (int-ℕ n)
  iff-le-int-ℕ m n = (preserves-le-int-ℕ m n , reflects-le-int-ℕ m n)
```

### Negation reverses the order of strict inequality of integers

```agda
abstract
  neg-le-ℤ : (x y : ℤ) → le-ℤ x y → le-ℤ (neg-ℤ y) (neg-ℤ x)
  neg-le-ℤ x y =
    tr
      ( is-positive-ℤ)
      ( ( ap (_+ℤ neg-ℤ x) (inv (neg-neg-ℤ y))) ∙
        ( commutative-add-ℤ (neg-ℤ (neg-ℤ y)) (neg-ℤ x)))
```
