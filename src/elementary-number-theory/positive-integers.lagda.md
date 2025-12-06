# The positive integers

```agda
module elementary-number-theory.positive-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-integers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-subtypes
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import set-theory.countable-sets
```

</details>

## Idea

The [integers](elementary-number-theory.integers.md) are defined as a
[disjoint sum](foundation-core.coproduct-types.md) of three components. A single
element component containing the integer _zero_, and two copies of the
[natural numbers](elementary-number-theory.natural-numbers.md), one copy for the
[negative integers](elementary-number-theory.negative-integers.md) and one copy
for the _positive integers_. Arranged on a number line, we have

```text
  ⋯  -4  -3  -2  -1   0   1   2   3   4   ⋯
  <---+---+---+---]   |   [---+---+---+--->
```

We say an integer is
{{#concept "positive" Disambiguation="integer" Agda=is-positive-ℤ}} if it is an
element of the positive component of the integers.

## Definitions

### Positive integers

```agda
is-positive-ℤ : ℤ → UU lzero
is-positive-ℤ (inl x) = empty
is-positive-ℤ (inr (inl x)) = empty
is-positive-ℤ (inr (inr x)) = unit

abstract
  is-prop-is-positive-ℤ : (x : ℤ) → is-prop (is-positive-ℤ x)
  is-prop-is-positive-ℤ (inl x) = is-prop-empty
  is-prop-is-positive-ℤ (inr (inl x)) = is-prop-empty
  is-prop-is-positive-ℤ (inr (inr x)) = is-prop-unit

subtype-positive-ℤ : subtype lzero ℤ
subtype-positive-ℤ x = (is-positive-ℤ x , is-prop-is-positive-ℤ x)

positive-ℤ : UU lzero
positive-ℤ = type-subtype subtype-positive-ℤ

ℤ⁺ : UU lzero
ℤ⁺ = positive-ℤ

is-positive-eq-ℤ : {x y : ℤ} → x ＝ y → is-positive-ℤ x → is-positive-ℤ y
is-positive-eq-ℤ = tr is-positive-ℤ

module _
  (p : positive-ℤ)
  where

  int-positive-ℤ : ℤ
  int-positive-ℤ = pr1 p

  int-ℤ⁺ : ℤ
  int-ℤ⁺ = int-positive-ℤ

  is-positive-int-positive-ℤ : is-positive-ℤ int-positive-ℤ
  is-positive-int-positive-ℤ = pr2 p

abstract
  eq-ℤ⁺ : (k l : ℤ⁺) → int-ℤ⁺ k ＝ int-ℤ⁺ l → k ＝ l
  eq-ℤ⁺ _ _ = eq-type-subtype subtype-positive-ℤ
```

### Positive constants

```agda
one-positive-ℤ : positive-ℤ
one-positive-ℤ = (one-ℤ , star)

one-ℤ⁺ : ℤ⁺
one-ℤ⁺ = one-positive-ℤ
```

## Properties

### Positivity is decidable

```agda
is-decidable-is-positive-ℤ : is-decidable-family is-positive-ℤ
is-decidable-is-positive-ℤ (inl x) = inr id
is-decidable-is-positive-ℤ (inr (inl x)) = inr id
is-decidable-is-positive-ℤ (inr (inr x)) = inl star

decidable-subtype-positive-ℤ : decidable-subtype lzero ℤ
decidable-subtype-positive-ℤ x =
  ( is-positive-ℤ x ,
    is-prop-is-positive-ℤ x ,
    is-decidable-is-positive-ℤ x)
```

### Positive integers are nonzero

```agda
is-nonzero-is-positive-ℤ : {x : ℤ} → is-positive-ℤ x → is-nonzero-ℤ x
is-nonzero-is-positive-ℤ {inr (inr x)} H ()
```

### The positive integers form a set

```agda
is-set-positive-ℤ : is-set positive-ℤ
is-set-positive-ℤ =
  is-set-type-subtype subtype-positive-ℤ is-set-ℤ

positive-ℤ-Set : Set lzero
positive-ℤ-Set = positive-ℤ , is-set-positive-ℤ
```

### The successor of a positive integer is positive

```agda
abstract
  is-positive-succ-is-positive-ℤ :
    {x : ℤ} → is-positive-ℤ x → is-positive-ℤ (succ-ℤ x)
  is-positive-succ-is-positive-ℤ {inr (inr x)} H = H

succ-positive-ℤ : positive-ℤ → positive-ℤ
succ-positive-ℤ (x , H) = (succ-ℤ x , is-positive-succ-is-positive-ℤ H)
```

### The integer image of a nonzero natural number is positive

```agda
abstract
  is-positive-int-is-nonzero-ℕ :
    (x : ℕ) → is-nonzero-ℕ x → is-positive-ℤ (int-ℕ x)
  is-positive-int-is-nonzero-ℕ zero-ℕ H = ex-falso (H refl)
  is-positive-int-is-nonzero-ℕ (succ-ℕ x) H = star

positive-int-ℕ⁺ : ℕ⁺ → positive-ℤ
positive-int-ℕ⁺ (n , n≠0) = int-ℕ n , is-positive-int-is-nonzero-ℕ n n≠0

positive-nat-ℤ⁺ : positive-ℤ → ℕ⁺
positive-nat-ℤ⁺ (inr (inr x) , k>0) = succ-nonzero-ℕ' x

abstract
  is-section-positive-nat-ℤ⁺ :
    (k : ℤ⁺) → positive-int-ℕ⁺ (positive-nat-ℤ⁺ k) ＝ k
  is-section-positive-nat-ℤ⁺ (inr (inr k) , k>0) =
    eq-type-subtype subtype-positive-ℤ refl

  is-retraction-positive-nat-ℤ⁺ :
    (n : ℕ⁺) → positive-nat-ℤ⁺ (positive-int-ℕ⁺ n) ＝ n
  is-retraction-positive-nat-ℤ⁺ (zero-ℕ , n≠0) = ex-falso (n≠0 refl)
  is-retraction-positive-nat-ℤ⁺ (succ-ℕ n , n≠0) = eq-nonzero-ℕ refl

  is-equiv-positive-int-ℕ⁺ : is-equiv positive-int-ℕ⁺
  is-equiv-positive-int-ℕ⁺ =
    is-equiv-is-invertible
      ( positive-nat-ℤ⁺)
      ( is-section-positive-nat-ℤ⁺)
      ( is-retraction-positive-nat-ℤ⁺)

equiv-positive-int-ℕ⁺ : ℕ⁺ ≃ ℤ⁺
equiv-positive-int-ℕ⁺ = (positive-int-ℕ⁺ , is-equiv-positive-int-ℕ⁺)
```

### The canonical equivalence between natural numbers and positive integers

```agda
positive-int-ℕ : ℕ → positive-ℤ
positive-int-ℕ = rec-ℕ one-positive-ℤ (λ _ → succ-positive-ℤ)

abstract
  int-positive-int-ℕ : (n : ℕ) → int-positive-ℤ (positive-int-ℕ n) ＝ in-pos-ℤ n
  int-positive-int-ℕ 0 = refl
  int-positive-int-ℕ (succ-ℕ n) = ap succ-ℤ (int-positive-int-ℕ n)

nat-positive-ℤ : positive-ℤ → ℕ
nat-positive-ℤ (inr (inr x) , H) = x

eq-nat-positive-succ-positive-ℤ :
  (x : positive-ℤ) →
  nat-positive-ℤ (succ-positive-ℤ x) ＝ succ-ℕ (nat-positive-ℤ x)
eq-nat-positive-succ-positive-ℤ (inr (inr x) , H) = refl

abstract
  is-section-nat-positive-ℤ :
    (x : positive-ℤ) → positive-int-ℕ (nat-positive-ℤ x) ＝ x
  is-section-nat-positive-ℤ (inr (inr zero-ℕ) , H) = refl
  is-section-nat-positive-ℤ (inr (inr (succ-ℕ x)) , H) =
    ap succ-positive-ℤ (is-section-nat-positive-ℤ ( inr (inr x) , H))

  is-retraction-nat-positive-ℤ :
    (n : ℕ) → nat-positive-ℤ (positive-int-ℕ n) ＝ n
  is-retraction-nat-positive-ℤ zero-ℕ = refl
  is-retraction-nat-positive-ℤ (succ-ℕ n) =
    eq-nat-positive-succ-positive-ℤ (positive-int-ℕ n) ∙
    ap succ-ℕ (is-retraction-nat-positive-ℤ n)

  is-equiv-positive-int-ℕ : is-equiv positive-int-ℕ
  is-equiv-positive-int-ℕ =
    is-equiv-is-invertible
      ( nat-positive-ℤ)
      ( is-section-nat-positive-ℤ)
      ( is-retraction-nat-positive-ℤ)

equiv-positive-int-ℕ : ℕ ≃ positive-ℤ
pr1 equiv-positive-int-ℕ = positive-int-ℕ
pr2 equiv-positive-int-ℕ = is-equiv-positive-int-ℕ
```

### The set of positive integers is countable

```agda
is-countable-positive-ℤ : is-countable positive-ℤ-Set
is-countable-positive-ℤ =
  is-countable-is-directly-countable
    ( positive-ℤ-Set)
    ( one-positive-ℤ)
    ( intro-exists
      ( positive-int-ℕ)
      ( is-surjective-is-equiv is-equiv-positive-int-ℕ))
```

### Zero is not positive

```agda
not-is-positive-zero-ℤ : ¬ (is-positive-ℤ zero-ℤ)
not-is-positive-zero-ℤ ()
```

## See also

- The relations between positive and nonnegative, negative and nonnpositive
  integers are derived in
  [`positive-and-negative-integers`](elementary-number-theory.positive-and-negative-integers.md)
