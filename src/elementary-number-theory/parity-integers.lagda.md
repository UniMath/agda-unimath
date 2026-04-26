# Parity of the integers

```agda
module elementary-number-theory.parity-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.unit-similarity-integers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negation
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

{{#concept "Parity" WD="parity" WDID=Q141160}}
[partitions](foundation.partitions.md) the
[integers](elementary-number-theory.integers.md) into two
[classes](foundation.equivalence-relations.md): the
{{#concept "even" Disambiguation="integer" Agda=is-even-ℤ WD="even number" WDID=Q13366104}}
and the
{{#concept "odd" Disambiguation="integer" Agda=is-odd-ℤ WD="odd number" WDID=Q13366129}}
integers. Even integers are those that are
[divisible](elementary-number-theory.divisibility-integers.md) by two, and odd
integers are those that aren't.

## Definitions

### Even integers

```agda
is-even-ℤ : ℤ → UU lzero
is-even-ℤ a = div-ℤ two-ℤ a
```

### The bi-infinite sequence of even integers

```agda
even-integer-ℤ : ℤ → ℤ
even-integer-ℤ a = two-ℤ *ℤ a
```

### Odd integers

```agda
is-odd-ℤ : ℤ → UU lzero
is-odd-ℤ a = ¬ (is-even-ℤ a)
```

### The bi-infinite sequence of odd integers

```agda
odd-integer-ℤ : ℤ → ℤ
odd-integer-ℤ a = two-ℤ *ℤ a +ℤ one-ℤ
```

### The type of odd expansions of an integer

```agda
has-odd-expansion-ℤ : ℤ → UU lzero
has-odd-expansion-ℤ = fiber odd-integer-ℤ
```

## Properties

### Even integers are closed under equality

```agda
is-even-eq-ℤ : {a b : ℤ} → a ＝ b → is-even-ℤ b → is-even-ℤ a
is-even-eq-ℤ refl H = H

is-even-eq-ℤ' : {a b : ℤ} → a ＝ b → is-even-ℤ a → is-even-ℤ b
is-even-eq-ℤ' refl H = H
```

### Odd integers are closed under equality

```agda
is-odd-eq-ℤ : {a b : ℤ} → a ＝ b → is-odd-ℤ b → is-odd-ℤ a
is-odd-eq-ℤ refl H = H

is-odd-eq-ℤ' : {a b : ℤ} → a ＝ b → is-odd-ℤ a → is-odd-ℤ b
is-odd-eq-ℤ' refl H = H
```

### A natural number is even if and only if it is even as an integer

```agda
is-even-int-is-even-ℕ : (n : ℕ) → is-even-ℕ n → is-even-ℤ (int-ℕ n)
is-even-int-is-even-ℕ n H = div-int-div-ℕ H

is-even-is-even-int-ℕ : (n : ℕ) → is-even-ℤ (int-ℕ n) → is-even-ℕ n
is-even-is-even-int-ℕ n H = div-div-int-ℕ H
```

### A natural number is odd if and only if it is odd as an integer

```agda
is-odd-int-is-odd-ℕ : (n : ℕ) → is-odd-ℕ n → is-odd-ℤ (int-ℕ n)
is-odd-int-is-odd-ℕ n H K = H (is-even-is-even-int-ℕ n K)

is-odd-is-odd-int-ℕ : (n : ℕ) → is-odd-ℤ (int-ℕ n) → is-odd-ℕ n
is-odd-is-odd-int-ℕ n H K = H (is-even-int-is-even-ℕ n K)
```

### An integer is even if and only if its absolute value is an even integer

```agda
is-even-int-abs-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-even-ℤ (int-abs-ℤ a)
is-even-int-abs-is-even-ℤ a =
  div-sim-unit-ℤ
    ( refl-sim-unit-ℤ two-ℤ)
    ( symmetric-sim-unit-ℤ (int-abs-ℤ a) a (sim-unit-abs-ℤ a))

is-even-is-even-int-abs-ℤ :
  (a : ℤ) → is-even-ℤ (int-abs-ℤ a) → is-even-ℤ a
is-even-is-even-int-abs-ℤ a =
  div-sim-unit-ℤ
    ( refl-sim-unit-ℤ two-ℤ)
    ( sim-unit-abs-ℤ a)

is-even-abs-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-even-ℕ (abs-ℤ a)
is-even-abs-is-even-ℤ a H =
  is-even-is-even-int-ℕ (abs-ℤ a) (is-even-int-abs-is-even-ℤ a H)

is-even-is-even-abs-ℤ :
  (a : ℤ) → is-even-ℕ (abs-ℤ a) → is-even-ℤ a
is-even-is-even-abs-ℤ a H =
  is-even-is-even-int-abs-ℤ a (is-even-int-is-even-ℕ (abs-ℤ a) H)
```

### An integer is odd if and only if its absolute value is an odd integer

```agda
is-odd-int-abs-is-odd-ℤ : (a : ℤ) → is-odd-ℤ a → is-odd-ℤ (int-abs-ℤ a)
is-odd-int-abs-is-odd-ℤ a H K = H (is-even-is-even-int-abs-ℤ a K)

is-odd-is-odd-int-abs-ℤ : (a : ℤ) → is-odd-ℤ (int-abs-ℤ a) → is-odd-ℤ a
is-odd-is-odd-int-abs-ℤ a H K = H (is-even-int-abs-is-even-ℤ a K)

is-odd-abs-is-odd-ℤ : (a : ℤ) → is-odd-ℤ a → is-odd-ℕ (abs-ℤ a)
is-odd-abs-is-odd-ℤ a H K = H (is-even-is-even-abs-ℤ a K)

is-odd-is-odd-abs-ℤ : (a : ℤ) → is-odd-ℕ (abs-ℤ a) → is-odd-ℤ a
is-odd-is-odd-abs-ℤ a H K = H (is-even-abs-is-even-ℤ a K)
```

### Being even or odd is decidable

```agda
is-decidable-is-even-ℤ :
  (a : ℤ) → is-decidable (is-even-ℤ a)
is-decidable-is-even-ℤ a =
  is-decidable-iff
    ( is-even-is-even-abs-ℤ a)
    ( is-even-abs-is-even-ℤ a)
    ( is-decidable-is-even-ℕ (abs-ℤ a))

is-decidable-is-odd-ℤ : (a : ℤ) → is-decidable (is-odd-ℤ a)
is-decidable-is-odd-ℤ a = is-decidable-neg (is-decidable-is-even-ℤ a)
```

### An integer is even if and only if it is not odd

```agda
is-even-is-not-odd-ℤ :
  (a : ℤ) → ¬ (is-odd-ℤ a) → is-even-ℤ a
is-even-is-not-odd-ℤ a =
  double-negation-elim-is-decidable (is-decidable-is-even-ℤ a)
```

### `0` is an even integer

```agda
is-even-zero-ℤ : is-even-ℤ zero-ℤ
is-even-zero-ℤ = is-even-int-is-even-ℕ 0 is-even-zero-ℕ
```

### `1` is an odd integer

```agda
is-odd-one-ℤ : is-odd-ℤ one-ℤ
is-odd-one-ℤ = is-odd-int-is-odd-ℕ 1 is-odd-one-ℕ
```

### `-1` is an odd integer

```agda
is-odd-neg-one-ℤ : is-odd-ℤ neg-one-ℤ
is-odd-neg-one-ℤ H =
  is-odd-one-ℤ (div-left-summand-ℤ two-ℤ one-ℤ neg-one-ℤ H is-even-zero-ℤ)
```

### `2` is an even integer

```agda
is-even-two-ℤ : is-even-ℤ two-ℤ
pr1 is-even-two-ℤ = one-ℤ
pr2 is-even-two-ℤ = refl
```

### `-2` is an even integer

```agda
is-even-neg-two-ℤ : is-even-ℤ neg-two-ℤ
pr1 is-even-neg-two-ℤ = neg-one-ℤ
pr2 is-even-neg-two-ℤ = refl
```

### An integer `x` is even if and only if `x + 2` is even

```agda
is-even-is-even-add-two-ℤ :
  (a : ℤ) → is-even-ℤ (a +ℤ two-ℤ) → is-even-ℤ a
is-even-is-even-add-two-ℤ a =
  div-left-summand-ℤ two-ℤ a two-ℤ (refl-div-ℤ two-ℤ)

is-even-is-even-succ-succ-ℤ :
  (a : ℤ) → is-even-ℤ (succ-ℤ (succ-ℤ a)) → is-even-ℤ a
is-even-is-even-succ-succ-ℤ a H =
  is-even-is-even-add-two-ℤ a
    ( tr
      ( is-even-ℤ)
      ( ap succ-ℤ (is-right-add-one-succ-ℤ a) ∙
        is-right-add-one-succ-ℤ _ ∙
        associative-add-ℤ a one-ℤ one-ℤ)
      ( H))

is-even-add-two-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-even-ℤ (a +ℤ two-ℤ)
is-even-add-two-is-even-ℤ a H =
  div-add-ℤ two-ℤ a two-ℤ H (refl-div-ℤ two-ℤ)

is-even-succ-succ-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-even-ℤ (succ-ℤ (succ-ℤ a))
is-even-succ-succ-is-even-ℤ a H =
  tr
    ( is-even-ℤ)
    ( inv (associative-add-ℤ a one-ℤ one-ℤ) ∙
      inv (is-right-add-one-succ-ℤ _) ∙
      inv (ap succ-ℤ (is-right-add-one-succ-ℤ a)))
    ( is-even-add-two-is-even-ℤ a H)
```

### An integer `x` is odd if and only if `x + 2` is odd

```agda
is-odd-is-odd-add-two-ℤ : (a : ℤ) → is-odd-ℤ (a +ℤ two-ℤ) → is-odd-ℤ a
is-odd-is-odd-add-two-ℤ a H K = H (is-even-add-two-is-even-ℤ a K)

is-odd-add-two-is-odd-ℤ : (a : ℤ) → is-odd-ℤ a → is-odd-ℤ (a +ℤ two-ℤ)
is-odd-add-two-is-odd-ℤ a H K = H (is-even-is-even-add-two-ℤ a K)
```

### Either `a` or `a + 1` is even

```agda
is-even-or-is-even-succ-ℤ :
  (a : ℤ) → is-even-ℤ a + is-even-ℤ (succ-ℤ a)
is-even-or-is-even-succ-ℤ (inl zero-ℕ) =
  inr is-even-zero-ℤ
is-even-or-is-even-succ-ℤ (inl (succ-ℕ x)) =
  map-coproduct
    ( λ H → is-even-is-even-succ-succ-ℤ (inl (succ-ℕ x)) H)
    ( id)
    ( map-commutative-coproduct (is-even-or-is-even-succ-ℤ (inl x)))
is-even-or-is-even-succ-ℤ (inr (inl star)) =
  inl is-even-zero-ℤ
is-even-or-is-even-succ-ℤ (inr (inr zero-ℕ)) =
  inr is-even-two-ℤ
is-even-or-is-even-succ-ℤ (inr (inr (succ-ℕ x))) =
  map-coproduct
    ( id)
    ( λ H → is-even-succ-succ-is-even-ℤ (inr (inr x)) H)
    ( map-commutative-coproduct (is-even-or-is-even-succ-ℤ (inr (inr x))))

is-even-or-is-even-add-one-ℤ :
  (a : ℤ) → is-even-ℤ a + is-even-ℤ (a +ℤ one-ℤ)
is-even-or-is-even-add-one-ℤ a =
  map-coproduct
    ( id)
    ( tr is-even-ℤ (is-right-add-one-succ-ℤ a))
    ( is-even-or-is-even-succ-ℤ a)
```

### Either `a` or `a - 1` is even

```agda
is-even-or-is-even-pred-ℤ :
  (a : ℤ) → is-even-ℤ a + is-even-ℤ (pred-ℤ a)
is-even-or-is-even-pred-ℤ a =
  map-commutative-coproduct
    ( map-coproduct
      ( id)
      ( tr is-even-ℤ (is-section-pred-ℤ a))
      ( is-even-or-is-even-succ-ℤ (pred-ℤ a)))

is-even-or-is-even-add-neg-one-ℤ :
  (a : ℤ) → is-even-ℤ a + is-even-ℤ (a +ℤ neg-one-ℤ)
is-even-or-is-even-add-neg-one-ℤ a =
  map-commutative-coproduct
    ( map-coproduct
      ( id)
      ( tr is-even-ℤ (is-section-right-add-neg-ℤ one-ℤ a))
      ( is-even-or-is-even-add-one-ℤ (a +ℤ neg-one-ℤ)))
```

### If an integer `x` is even, then `x + 1` is odd

```agda
is-odd-add-one-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-odd-ℤ (a +ℤ one-ℤ)
is-odd-add-one-is-even-ℤ a H K =
  is-odd-one-ℤ (div-right-summand-ℤ two-ℤ a one-ℤ H K)
```

### If an integer `x` is even, then `x - 1` is odd

```agda
is-odd-add-neg-one-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-odd-ℤ (a -ℤ one-ℤ)
is-odd-add-neg-one-is-even-ℤ a H K =
  is-odd-neg-one-ℤ (div-right-summand-ℤ two-ℤ a neg-one-ℤ H K)
```

### If an integer `x + 1` is even, then `x` is odd

```agda
is-odd-is-even-add-one-ℤ :
  (a : ℤ) → is-even-ℤ (a +ℤ one-ℤ) → is-odd-ℤ a
is-odd-is-even-add-one-ℤ a H K =
  is-odd-one-ℤ (div-right-summand-ℤ two-ℤ a one-ℤ K H)
```

### If an integer `a - 1` is even, then `a` is odd

```agda
is-odd-is-even-add-neg-one-ℤ :
  (a : ℤ) → is-even-ℤ (a -ℤ one-ℤ) → is-odd-ℤ a
is-odd-is-even-add-neg-one-ℤ a H K =
  is-odd-neg-one-ℤ (div-right-summand-ℤ two-ℤ a neg-one-ℤ K H)
```

### If an integer `x` is odd, then `x + 1` is even

```agda
is-even-add-one-is-odd-ℤ :
  (a : ℤ) → is-odd-ℤ a → is-even-ℤ (a +ℤ one-ℤ)
is-even-add-one-is-odd-ℤ a H =
  map-left-unit-law-coproduct-is-empty
    ( is-even-ℤ a)
    ( is-even-ℤ (a +ℤ one-ℤ))
    ( H)
    ( is-even-or-is-even-add-one-ℤ a)
```

### If an integer is even, then its predecessor is odd

```agda
is-odd-pred-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-odd-ℤ (pred-ℤ a)
is-odd-pred-is-even-ℤ a H =
  is-odd-eq-ℤ (is-right-add-neg-one-pred-ℤ a) (is-odd-add-neg-one-is-even-ℤ a H)
```

### If the successor of an integer `a` is even, then `a` is odd

```agda
is-odd-is-even-succ-ℤ :
  (a : ℤ) → is-even-ℤ (succ-ℤ a) → is-odd-ℤ a
is-odd-is-even-succ-ℤ a H =
  is-odd-is-even-add-one-ℤ a (is-even-eq-ℤ' (is-right-add-one-succ-ℤ a) H)
```

### If the predecessor of an integer is even, then it is odd

```agda
is-odd-is-even-pred-ℤ :
  (a : ℤ) → is-even-ℤ (pred-ℤ a) → is-odd-ℤ a
is-odd-is-even-pred-ℤ a H =
  is-odd-is-even-add-neg-one-ℤ a
    ( is-even-eq-ℤ' (is-right-add-neg-one-pred-ℤ a) H)
```

### If an integer `x + 1` is odd, then `x` is even

```agda
is-even-is-odd-add-one-ℤ :
  (a : ℤ) → is-odd-ℤ (a +ℤ one-ℤ) → is-even-ℤ a
is-even-is-odd-add-one-ℤ a H =
  map-right-unit-law-coproduct-is-empty
    ( is-even-ℤ a)
    ( is-even-ℤ (a +ℤ one-ℤ))
    ( H)
    ( is-even-or-is-even-add-one-ℤ a)
```

### An integer is odd if and only if it has an odd expansion

```agda
is-odd-has-odd-expansion-ℤ : (a : ℤ) → has-odd-expansion-ℤ a → is-odd-ℤ a
is-odd-has-odd-expansion-ℤ ._ (x , refl) =
  is-odd-add-one-is-even-ℤ (two-ℤ *ℤ x) (x , commutative-mul-ℤ x two-ℤ)

has-odd-expansion-is-odd-ℤ :
  (a : ℤ) → is-odd-ℤ a → has-odd-expansion-ℤ a
has-odd-expansion-is-odd-ℤ a H
  with
  map-left-unit-law-coproduct-is-empty
    ( is-even-ℤ a)
    ( is-even-ℤ (a +ℤ neg-one-ℤ))
    ( H)
    ( is-even-or-is-even-add-neg-one-ℤ a)
... | (k , p) =
  ( k ,
    ap (_+ℤ one-ℤ) (commutative-mul-ℤ two-ℤ k ∙ p) ∙
    is-section-right-add-neg-ℤ one-ℤ a)
```

### An integer is even if and only if it is divisible by an even integer

```agda
is-even-div-is-even-ℤ :
  (a b : ℤ) → is-even-ℤ a → div-ℤ a b → is-even-ℤ b
is-even-div-is-even-ℤ a b H K =
  transitive-div-ℤ two-ℤ a b K H

is-even-div-four-ℤ :
  (a : ℤ) → div-ℤ (int-ℕ 4) a → is-even-ℤ a
is-even-div-four-ℤ a =
  is-even-div-is-even-ℤ (int-ℕ 4) a (two-ℤ , refl)
```

### If any two out of `x`, `y`, and `x + y` are even, then so is the third

```agda
is-even-add-ℤ :
  (a b : ℤ) → is-even-ℤ a → is-even-ℤ b → is-even-ℤ (a +ℤ b)
is-even-add-ℤ = div-add-ℤ two-ℤ

is-even-left-summand-ℤ :
  (a b : ℤ) → is-even-ℤ b → is-even-ℤ (a +ℤ b) → is-even-ℤ a
is-even-left-summand-ℤ = div-left-summand-ℤ two-ℤ

is-even-right-summand-ℤ :
  (a b : ℤ) → is-even-ℤ a → is-even-ℤ (a +ℤ b) → is-even-ℤ b
is-even-right-summand-ℤ = div-right-summand-ℤ two-ℤ
```
