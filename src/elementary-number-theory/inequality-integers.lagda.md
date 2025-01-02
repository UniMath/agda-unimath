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
preserves-order-left-add-ℤ :
  (z x y : ℤ) → leq-ℤ x y → leq-ℤ (x +ℤ z) (y +ℤ z)
preserves-order-left-add-ℤ z x y =
  is-nonnegative-eq-ℤ (inv (right-translation-diff-ℤ y x z))

preserves-order-right-add-ℤ :
  (z x y : ℤ) → leq-ℤ x y → leq-ℤ (z +ℤ x) (z +ℤ y)
preserves-order-right-add-ℤ z x y =
  is-nonnegative-eq-ℤ (inv (left-translation-diff-ℤ y x z))

preserves-order-add-ℤ :
  {a b c d : ℤ} → leq-ℤ a b → leq-ℤ c d → leq-ℤ (a +ℤ c) (b +ℤ d)
preserves-order-add-ℤ {a} {b} {c} {d} H K =
  transitive-leq-ℤ
    ( a +ℤ c)
    ( b +ℤ c)
    ( b +ℤ d)
    ( preserves-order-right-add-ℤ b c d K)
    ( preserves-order-left-add-ℤ c a b H)
```

### Addition on the integers reflects inequality

```agda
reflects-order-left-add-ℤ :
  (z x y : ℤ) → leq-ℤ (x +ℤ z) (y +ℤ z) → leq-ℤ x y
reflects-order-left-add-ℤ z x y =
  is-nonnegative-eq-ℤ (right-translation-diff-ℤ y x z)

reflects-order-right-add-ℤ :
  (z x y : ℤ) → leq-ℤ (z +ℤ x) (z +ℤ y) → leq-ℤ x y
reflects-order-right-add-ℤ z x y =
  is-nonnegative-eq-ℤ (left-translation-diff-ℤ y x z)
```

### The inclusion of ℕ into ℤ preserves inequality

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

### Transposing summands in inequalities

```agda
transpose-left-summand-leq-ℤ :
  (a b c : ℤ) → a ≤-ℤ b +ℤ c → neg-ℤ b +ℤ a ≤-ℤ c
transpose-left-summand-leq-ℤ a b c H =
  reflects-order-right-add-ℤ b
    ( neg-ℤ b +ℤ a)
    ( c)
    ( concatenate-eq-leq-ℤ (b +ℤ c) (is-section-left-add-neg-ℤ b a) H)

inv-transpose-left-summand-leq-ℤ :
  (a b c : ℤ) → neg-ℤ b +ℤ a ≤-ℤ c → a ≤-ℤ b +ℤ c
inv-transpose-left-summand-leq-ℤ a b c H =
  concatenate-eq-leq-ℤ
    ( b +ℤ c)
    ( inv (is-section-left-add-neg-ℤ b a))
    ( preserves-order-right-add-ℤ b (neg-ℤ b +ℤ a) c H)

transpose-left-summand-leq-ℤ' :
  (a b c : ℤ) → b +ℤ a ≤-ℤ c → a ≤-ℤ neg-ℤ b +ℤ c
transpose-left-summand-leq-ℤ' a b c H =
  inv-transpose-left-summand-leq-ℤ a (neg-ℤ b) c
    ( concatenate-eq-leq-ℤ c (ap (add-ℤ' a) (neg-neg-ℤ b)) H)

inv-transpose-left-summand-leq-ℤ' :
  (a b c : ℤ) → a ≤-ℤ neg-ℤ b +ℤ c → b +ℤ a ≤-ℤ c
inv-transpose-left-summand-leq-ℤ' a b c H =
  concatenate-eq-leq-ℤ c
    ( ap (add-ℤ' a) (inv (neg-neg-ℤ b)))
    ( transpose-left-summand-leq-ℤ a (neg-ℤ b) c H)

transpose-right-summand-leq-ℤ :
  (a b c : ℤ) → a ≤-ℤ b +ℤ c → a +ℤ neg-ℤ c ≤-ℤ b
transpose-right-summand-leq-ℤ a b c H =
  reflects-order-left-add-ℤ c
    ( a +ℤ neg-ℤ c)
    ( b)
    ( concatenate-eq-leq-ℤ (b +ℤ c) (is-section-right-add-neg-ℤ c a) H)

inv-transpose-right-summand-leq-ℤ :
  (a b c : ℤ) → a +ℤ neg-ℤ c ≤-ℤ b → a ≤-ℤ b +ℤ c
inv-transpose-right-summand-leq-ℤ a b c H =
  concatenate-eq-leq-ℤ
    ( b +ℤ c)
    ( inv (is-section-right-add-neg-ℤ c a))
    ( preserves-order-left-add-ℤ c (a +ℤ neg-ℤ c) b H)

transpose-right-summand-leq-ℤ' :
  (a b c : ℤ) → a +ℤ c ≤-ℤ b → a ≤-ℤ b +ℤ neg-ℤ c
transpose-right-summand-leq-ℤ' a b c H =
  inv-transpose-right-summand-leq-ℤ a b
    ( neg-ℤ c)
    ( concatenate-eq-leq-ℤ b (ap (add-ℤ a) (neg-neg-ℤ c)) H)

inv-transpose-right-summand-leq-ℤ' :
  (a b c : ℤ) → a ≤-ℤ b +ℤ neg-ℤ c → a +ℤ c ≤-ℤ b
inv-transpose-right-summand-leq-ℤ' a b c H =
  concatenate-eq-leq-ℤ b
    ( ap (add-ℤ a) (inv (neg-neg-ℤ c)))
    ( transpose-right-summand-leq-ℤ a b (neg-ℤ c) H)
```

### The operation taking integers to their negatives reverses their order

**Proof.** If `a ≤ b`, then `b - a` is nonnegative. Note that `b - a ＝ (-a) - (-b)`, which is therefore also nonnegative, implying that `-b ≤ -a`.

```agda
reverses-order-neg-ℤ :
  (a b : ℤ) → a ≤-ℤ b → neg-ℤ b ≤-ℤ neg-ℤ a
reverses-order-neg-ℤ a b =
  tr
    ( is-nonnegative-ℤ)
    ( ( commutative-add-ℤ b (neg-ℤ a)) ∙
      ( ap (add-ℤ (neg-ℤ a)) (inv (neg-neg-ℤ b))))
```

### The operation taking integers to their negative reversely reflects their order

```agda
reversely-reflects-order-neg-ℤ :
  (a b : ℤ) → neg-ℤ a ≤-ℤ neg-ℤ b → b ≤-ℤ a
reversely-reflects-order-neg-ℤ a b =
  tr
    ( is-nonnegative-ℤ)
    ( ap (add-ℤ (neg-ℤ b)) (neg-neg-ℤ a) ∙ commutative-add-ℤ (neg-ℤ b) a)
```

### Transposing negatives in inequalities

```agda
transpose-right-neg-leq-ℤ :
  (a b : ℤ) → b ≤-ℤ neg-ℤ a → a ≤-ℤ neg-ℤ b
transpose-right-neg-leq-ℤ a b H =
  reversely-reflects-order-neg-ℤ
    ( neg-ℤ b)
    ( a)
    ( concatenate-eq-leq-ℤ (neg-ℤ a) (neg-neg-ℤ b) H)

transpose-left-neg-leq-ℤ :
  (a b : ℤ) → neg-ℤ b ≤-ℤ a → neg-ℤ a ≤-ℤ b
transpose-left-neg-leq-ℤ a b H =
  reversely-reflects-order-neg-ℤ b
    ( neg-ℤ a)
    ( concatenate-leq-eq-ℤ (neg-ℤ b) H (inv (neg-neg-ℤ a)))
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

## See also

- The decidable total order on the integers is defined in
  [`decidable-total-order-integers`](elementary-number-theory.decidable-total-order-integers.md)
- Strict inequality on the integers is defined in
  [`strict-inequality-integers`](elementary-number-theory.strict-inequality-integers.md)
