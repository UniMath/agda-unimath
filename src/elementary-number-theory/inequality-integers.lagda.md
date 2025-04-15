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
open import foundation.binary-transport
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

An [integer](elementary-number-theory.integers.md) `x` is _less than or equal_
to the integer `y` if the
[difference](elementary-number-theory.difference-integers.md) `y - x` is
[nonnegative](elementary-number-theory.nonnegative-integers.md). This relation
defines the
{{#concept "standard ordering" Disambiguation="integers" Agda=leq-ℤ}} on the
integers.

## Definition

### Inequality on the integers

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
```

### Inequality on the integers is decidable

```agda
is-decidable-leq-ℤ : (x y : ℤ) → (leq-ℤ x y) + ¬ (leq-ℤ x y)
is-decidable-leq-ℤ x y = is-decidable-is-nonnegative-ℤ (y -ℤ x)

leq-ℤ-Decidable-Prop : (x y : ℤ) → Decidable-Prop lzero
leq-ℤ-Decidable-Prop x y =
  ( leq-ℤ x y ,
    is-prop-leq-ℤ x y ,
    is-decidable-leq-ℤ x y)
```

### Inequality on the integers is linear

```agda
linear-leq-ℤ : (x y : ℤ) → (leq-ℤ x y) + (leq-ℤ y x)
linear-leq-ℤ x y =
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

### Addition on the integers preserves inequality

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
```

### Addition on the integers reflects inequality

```agda
reflects-leq-left-add-ℤ :
  (z x y : ℤ) → leq-ℤ (x +ℤ z) (y +ℤ z) → leq-ℤ x y
reflects-leq-left-add-ℤ z x y =
  is-nonnegative-eq-ℤ (right-translation-diff-ℤ y x z)

reflects-leq-right-add-ℤ :
  (z x y : ℤ) → leq-ℤ (z +ℤ x) (z +ℤ y) → leq-ℤ x y
reflects-leq-right-add-ℤ z x y =
  is-nonnegative-eq-ℤ (left-translation-diff-ℤ y x z)
```

### The successor function reflects inequality

```agda
reflects-leq-succ-ℤ :
  (x y : ℤ) → leq-ℤ (succ-ℤ x) (succ-ℤ y) → leq-ℤ x y
reflects-leq-succ-ℤ x y H =
  reflects-leq-left-add-ℤ
    ( one-ℤ)
    ( x)
    ( y)
    ( binary-tr
      ( leq-ℤ)
      ( is-right-add-one-succ-ℤ x)
      ( is-right-add-one-succ-ℤ y)
      ( H))
```

### Zero is lesser than or equal to all the integer images of natural numbers

```agda
leq-zero-int-ℕ : (n : ℕ) → leq-ℤ zero-ℤ (int-ℕ n)
leq-zero-int-ℕ zero-ℕ = refl-leq-ℤ zero-ℤ
leq-zero-int-ℕ (succ-ℕ n) =
  transitive-leq-ℤ
    ( zero-ℤ)
    ( int-ℕ n)
    ( in-pos-ℤ n)
    ( tr (leq-ℤ (int-ℕ n)) (succ-int-ℕ n) (succ-leq-ℤ (int-ℕ n)))
    ( leq-zero-int-ℕ n)
```

### The inclusion of ℕ into ℤ preserves and reflects inequality

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

leq-int-leq-in-pos-ℤ :
  (x y : ℕ) → leq-ℤ (in-pos-ℤ x) (in-pos-ℤ y) → leq-ℤ (int-ℕ x) (int-ℕ y)
leq-int-leq-in-pos-ℤ zero-ℕ zero-ℕ H = refl-leq-ℤ zero-ℤ
leq-int-leq-in-pos-ℤ zero-ℕ (succ-ℕ y) H = leq-zero-int-ℕ (succ-ℕ y)
leq-int-leq-in-pos-ℤ (succ-ℕ x) (succ-ℕ y) H =
  reflects-leq-succ-ℤ (in-pos-ℤ x) (in-pos-ℤ y) H

reflects-leq-int-ℕ : (x y : ℕ) → leq-ℤ (int-ℕ x) (int-ℕ y) → leq-ℕ x y
reflects-leq-int-ℕ zero-ℕ zero-ℕ H = star
reflects-leq-int-ℕ zero-ℕ (succ-ℕ y) H = star
reflects-leq-int-ℕ (succ-ℕ x) (succ-ℕ y) H =
  reflects-leq-int-ℕ x y (leq-int-leq-in-pos-ℤ x y H)
```

### The partially ordered set of integers ordered by inequality

```agda
ℤ-Preorder : Preorder lzero lzero
ℤ-Preorder =
  (ℤ , leq-ℤ-Prop , refl-leq-ℤ , transitive-leq-ℤ)

ℤ-Poset : Poset lzero lzero
ℤ-Poset = (ℤ-Preorder , λ x y → antisymmetric-leq-ℤ)
```

### An integer `x` is nonnegative if and only if `0 ≤ x`

```agda
module _
  (x : ℤ)
  where

  abstract
    leq-zero-is-nonnegative-ℤ : is-nonnegative-ℤ x → leq-ℤ zero-ℤ x
    leq-zero-is-nonnegative-ℤ =
      is-nonnegative-eq-ℤ (inv (right-zero-law-diff-ℤ x))

    is-nonnegative-leq-zero-ℤ : leq-ℤ zero-ℤ x → is-nonnegative-ℤ x
    is-nonnegative-leq-zero-ℤ =
      is-nonnegative-eq-ℤ (right-zero-law-diff-ℤ x)
```

### An integer greater than or equal to a nonnegative integer is nonnegative

```agda
module _
  (x y : ℤ) (I : leq-ℤ x y)
  where

  abstract
    is-nonnegative-leq-nonnegative-ℤ : is-nonnegative-ℤ x → is-nonnegative-ℤ y
    is-nonnegative-leq-nonnegative-ℤ H =
      is-nonnegative-leq-zero-ℤ y
        ( transitive-leq-ℤ
          ( zero-ℤ)
          ( x)
          ( y)
          ( I)
          ( leq-zero-is-nonnegative-ℤ x H))
```

### An integer `x` is nonpositive if and only if `x ≤ 0`

```agda
module _
  (x : ℤ)
  where

  abstract
    leq-zero-is-nonpositive-ℤ : is-nonpositive-ℤ x → leq-ℤ x zero-ℤ
    leq-zero-is-nonpositive-ℤ = is-nonnegative-neg-is-nonpositive-ℤ

    is-nonpositive-leq-zero-ℤ : leq-ℤ x zero-ℤ → is-nonpositive-ℤ x
    is-nonpositive-leq-zero-ℤ H =
      is-nonpositive-eq-ℤ
        ( neg-neg-ℤ x)
        ( is-nonpositive-neg-is-nonnegative-ℤ H)
```

### An integer less than or equal to a nonpositive integer is nonpositive

```agda
module _
  (x y : ℤ) (I : leq-ℤ x y)
  where

  abstract
    is-nonpositive-leq-nonpositive-ℤ : is-nonpositive-ℤ y → is-nonpositive-ℤ x
    is-nonpositive-leq-nonpositive-ℤ H =
      is-nonpositive-leq-zero-ℤ x
        ( transitive-leq-ℤ
          ( x)
          ( y)
          ( zero-ℤ)
          ( leq-zero-is-nonpositive-ℤ y H)
          ( I))
```

### Negation of integers reverses inequality

```agda
neg-leq-ℤ : (x y : ℤ) → leq-ℤ x y → leq-ℤ (neg-ℤ y) (neg-ℤ x)
neg-leq-ℤ x y =
  tr
    ( is-nonnegative-ℤ)
    ( ap (_+ℤ neg-ℤ x) (inv (neg-neg-ℤ y)) ∙
      commutative-add-ℤ (neg-ℤ (neg-ℤ y)) (neg-ℤ x))
```

## See also

- The decidable total order on the integers is defined in
  [`decidable-total-order-integers`](elementary-number-theory.decidable-total-order-integers.md)
- Strict inequality on the integers is defined in
  [`strict-inequality-integers`](elementary-number-theory.strict-inequality-integers.md)
