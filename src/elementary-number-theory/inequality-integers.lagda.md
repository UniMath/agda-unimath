# Inequality on the integers

```agda
module elementary-number-theory.inequality-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-positive-and-negative-integers
open import elementary-number-theory.difference-integers
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

The comparison of two integers is given by the sign of their difference.

## Definition

### The ordering on ℤ

```agda
leq-ℤ-Prop : ℤ → ℤ → Prop lzero
leq-ℤ-Prop x y = subtype-nonnegative-ℤ (y -ℤ x)

leq-ℤ : ℤ → ℤ → UU lzero
leq-ℤ x y = type-Prop (leq-ℤ-Prop x y)

is-prop-leq-ℤ : (x y : ℤ) → is-prop (leq-ℤ x y)
is-prop-leq-ℤ x y = is-prop-type-Prop (leq-ℤ-Prop x y)

infix 30 _≤-ℤ_
_≤-ℤ_ = leq-ℤ
```

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

### Inequality on the integers is reflexive, antisymmetric and transitive

```agda
refl-leq-ℤ : (k : ℤ) → leq-ℤ k k
refl-leq-ℤ k = tr is-nonnegative-ℤ (inv (right-inverse-law-add-ℤ k)) star

antisymmetric-leq-ℤ : {x y : ℤ} → leq-ℤ x y → leq-ℤ y x → x ＝ y
antisymmetric-leq-ℤ {x} {y} H K =
  eq-diff-ℤ
    ( is-zero-is-nonnegative-neg-is-nonnegative-ℤ K
      ( is-nonnegative-eq-ℤ (inv (distributive-neg-diff-ℤ x y)) H))

transitive-leq-ℤ : (k l m : ℤ) → leq-ℤ l m → leq-ℤ k l → leq-ℤ k m
transitive-leq-ℤ k l m H K =
  is-nonnegative-eq-ℤ
    ( triangle-diff-ℤ m l k)
    ( is-nonnegative-add-ℤ H K)

trans-leq-ℤ : {k l m : ℤ} → leq-ℤ l m → leq-ℤ k l → leq-ℤ k m
trans-leq-ℤ {k} {l} {m} = transitive-leq-ℤ k l m

ℤ-Preorder : Preorder lzero lzero
ℤ-Preorder =
  (ℤ , leq-ℤ-Prop , refl-leq-ℤ , transitive-leq-ℤ)

ℤ-Poset : Poset lzero lzero
ℤ-Poset = (ℤ-Preorder , λ x y → antisymmetric-leq-ℤ)
```

### The ordering of the integers is decidable

```agda
is-decidable-leq-ℤ : (x y : ℤ) → (leq-ℤ x y) + ¬ (leq-ℤ x y)
is-decidable-leq-ℤ x y = is-decidable-is-nonnegative-ℤ (y -ℤ x)

leq-ℤ-Decidable-Prop : (x y : ℤ) → Decidable-Prop lzero
leq-ℤ-Decidable-Prop x y =
  ( leq-ℤ x y ,
    is-prop-leq-ℤ x y ,
    is-decidable-leq-ℤ x y)
```

### The ordering of the integers is total

```agda
total-leq-ℤ : {x y : ℤ} → (leq-ℤ x y) + (leq-ℤ y x)
total-leq-ℤ {x} {y} =
  map-coproduct
    ( λ H →
      is-nonnegative-is-positive-ℤ
        ( is-positive-eq-ℤ
          ( distributive-neg-diff-ℤ x y)
          ( is-positive-neg-is-negative-ℤ H)))
    ( id)
    ( decide-is-negative-is-nonnegative-ℤ)
```

### An integer is lesser than its successor

```agda
succ-leq-ℤ : (k : ℤ) → leq-ℤ k (succ-ℤ k)
succ-leq-ℤ k =
  is-nonnegative-eq-ℤ
    ( inv
      ( ( left-successor-law-add-ℤ k (neg-ℤ k)) ∙
        ( ap succ-ℤ (right-inverse-law-add-ℤ k))))
    ( star)

leq-ℤ-succ-leq-ℤ : (k l : ℤ) → leq-ℤ k l → leq-ℤ k (succ-ℤ l)
leq-ℤ-succ-leq-ℤ k l = transitive-leq-ℤ k l (succ-ℤ l) (succ-leq-ℤ l)
```

### Chaining rules for equality and inequality

```agda
concatenate-eq-leq-eq-ℤ :
  {x' x y y' : ℤ} → x' ＝ x → leq-ℤ x y → y ＝ y' → leq-ℤ x' y'
concatenate-eq-leq-eq-ℤ refl H refl = H

concatenate-leq-eq-ℤ :
  (x : ℤ) {y y' : ℤ} → leq-ℤ x y → y ＝ y' → leq-ℤ x y'
concatenate-leq-eq-ℤ x H refl = H

concatenate-eq-leq-ℤ :
  {x x' : ℤ} (y : ℤ) → x' ＝ x → leq-ℤ x y → leq-ℤ x' y
concatenate-eq-leq-ℤ y refl H = H
```

### ℤ is an ordered ring

```agda
preserves-leq-left-add-ℤ :
  (z x y : ℤ) → leq-ℤ x y → leq-ℤ (x +ℤ z) (y +ℤ z)
preserves-leq-left-add-ℤ z x y =
  is-nonnegative-eq-ℤ (inv (right-translation-diff-ℤ y x z))

preserves-leq-right-add-ℤ :
  (z x y : ℤ) → leq-ℤ x y → leq-ℤ (z +ℤ x) (z +ℤ y)
preserves-leq-right-add-ℤ z x y =
  is-nonnegative-eq-ℤ (inv (left-translation-diff-ℤ y x z))

preserves-leq-add-ℤ :
  {a b c d : ℤ} → leq-ℤ a b → leq-ℤ c d → leq-ℤ (a +ℤ c) (b +ℤ d)
preserves-leq-add-ℤ {a} {b} {c} {d} H K =
  transitive-leq-ℤ
    ( a +ℤ c)
    ( b +ℤ c)
    ( b +ℤ d)
    ( preserves-leq-right-add-ℤ b c d K)
    ( preserves-leq-left-add-ℤ c a b H)

reflects-leq-left-add-ℤ :
  (z x y : ℤ) → leq-ℤ (x +ℤ z) (y +ℤ z) → leq-ℤ x y
reflects-leq-left-add-ℤ z x y =
  is-nonnegative-eq-ℤ (right-translation-diff-ℤ y x z)

reflects-leq-right-add-ℤ :
  (z x y : ℤ) → leq-ℤ (z +ℤ x) (z +ℤ y) → leq-ℤ x y
reflects-leq-right-add-ℤ z x y =
  is-nonnegative-eq-ℤ (left-translation-diff-ℤ y x z)
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

### Strict inequality implies inequality

```agda
leq-le-ℤ : {x y : ℤ} → le-ℤ x y → leq-ℤ x y
leq-le-ℤ {x} {y} = is-nonnegative-is-positive-ℤ
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

### Inclusion of ℕ into ℤ preserves order

```agda
leq-int-ℕ : (x y : ℕ) → leq-ℕ x y → leq-ℤ (int-ℕ x) (int-ℕ y)
leq-int-ℕ zero-ℕ y H =
  tr
    ( is-nonnegative-ℤ)
    ( inv (right-unit-law-add-ℤ (int-ℕ y)))
    ( is-nonnegative-int-ℕ y)
leq-int-ℕ (succ-ℕ x) (succ-ℕ y) H = tr (is-nonnegative-ℤ)
  ( inv (diff-succ-ℤ (int-ℕ y) (int-ℕ x)) ∙
    ( ap (_-ℤ (succ-ℤ (int-ℕ x))) (succ-int-ℕ y) ∙
      ap ((int-ℕ (succ-ℕ y)) -ℤ_) (succ-int-ℕ x)))
  ( leq-int-ℕ x y H)
```
