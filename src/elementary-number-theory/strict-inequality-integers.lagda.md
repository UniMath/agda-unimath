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

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
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

An [integer](elementary-number-theory.integers.md) `x` is _strictly less than_ the integer `y` if the [difference](elementary-number-theory.difference-integers.md) `y - x` is [positive](elementary-number-theory.positive-integers.md). This relation defines the {{#concept "standard strict ordering" Disambiguation="integers" Agda=leq-ℤ}} on the integers.

## Definition

### The strict ordering on ℤ

```agda
le-ℤ-Prop : ℤ → ℤ → Prop lzero
le-ℤ-Prop x y = subtype-positive-ℤ (y -ℤ x)

le-ℤ : ℤ → ℤ → UU lzero
le-ℤ x y = type-Prop (le-ℤ-Prop x y)

is-prop-le-ℤ : (x y : ℤ) → is-prop (le-ℤ x y)
is-prop-le-ℤ x y = is-prop-type-Prop (le-ℤ-Prop x y)
```

## Properties

### Strict inequality implies inequality

```agda
leq-le-ℤ : {x y : ℤ} → le-ℤ x y → leq-ℤ x y
leq-le-ℤ {x} {y} = is-nonnegative-is-positive-ℤ
```

### The strict ordering on the integers is decidable

```agda
is-decidable-le-ℤ : (x y : ℤ) → (le-ℤ x y) + ¬ (le-ℤ x y)
is-decidable-le-ℤ x y = is-decidable-is-positive-ℤ (y -ℤ x)

le-ℤ-Decidable-Prop : (x y : ℤ) → Decidable-Prop lzero
le-ℤ-Decidable-Prop x y =
  ( le-ℤ x y ,
    is-prop-le-ℤ x y ,
    is-decidable-le-ℤ x y)
```

### Strict inequality on the integers is transitive and asymmetric

```agda
transitive-le-ℤ : (k l m : ℤ) → le-ℤ l m → le-ℤ k l → le-ℤ k m
transitive-le-ℤ k l m H K =
  is-positive-eq-ℤ
    ( triangle-diff-ℤ m l k)
    ( is-positive-add-ℤ H K)

asymmetric-le-ℤ : (x y : ℤ) → le-ℤ x y → ¬ (le-ℤ y x)
asymmetric-le-ℤ x y p =
  is-not-positive-is-nonpositive-ℤ
    ( is-nonpositive-eq-ℤ
      ( distributive-neg-diff-ℤ y x)
      ( is-nonpositive-neg-is-nonnegative-ℤ
        ( is-nonnegative-is-positive-ℤ p)))
```

### The strict ordering on the integers is connected

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

### An integer is strictly greater than its predecessor

```agda
le-pred-ℤ : (x : ℤ) → le-ℤ (pred-ℤ x) x
le-pred-ℤ x =
  is-positive-eq-ℤ
    ( inv (right-predecessor-law-diff-ℤ x x ∙ ap succ-ℤ (is-zero-diff-ℤ' x)))
    ( is-positive-int-positive-ℤ one-positive-ℤ)
```

### An integer is strictly lesser than its successor

```agda
le-succ-ℤ : (x : ℤ) → le-ℤ x (succ-ℤ x)
le-succ-ℤ x =
  is-positive-eq-ℤ
    ( inv (left-successor-law-diff-ℤ x x ∙ ap succ-ℤ (is-zero-diff-ℤ' x)))
    ( is-positive-int-positive-ℤ one-positive-ℤ)
```

### Addition on the integers preserves and reflects the strict ordering

```agda
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

reflects-le-left-add-ℤ :
  (z x y : ℤ) → le-ℤ (x +ℤ z) (y +ℤ z) → le-ℤ x y
reflects-le-left-add-ℤ z x y =
  is-positive-eq-ℤ (right-translation-diff-ℤ y x z)

reflects-le-right-add-ℤ :
  (z x y : ℤ) → le-ℤ (z +ℤ x) (z +ℤ y) → le-ℤ x y
reflects-le-right-add-ℤ z x y =
  is-positive-eq-ℤ (left-translation-diff-ℤ y x z)
```
