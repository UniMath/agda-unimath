# Strictly increasing sequences of natural numbers

```agda
module elementary-number-theory.strictly-increasing-sequences-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Strictly increasing sequences of natural numbers are sequences `f : ℕ → ℕ` that
preserve inequality of natural numbers.

The identity sequence is strictly increasing. Strictly increasing sequences of
natural numbers are stable under composition. Strictly increasing sequences of
natural numbers and can get arbitrarily large.

## Definitions

### Strictly increasing sequences of natural numbers

```agda
module _
  (f : sequence ℕ)
  where

  is-strict-increasing-sequence-prop-ℕ : Prop lzero
  is-strict-increasing-sequence-prop-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (le-ℕ-Prop i j) (le-ℕ-Prop (f i) (f j))))

  is-strict-increasing-sequence-ℕ : UU lzero
  is-strict-increasing-sequence-ℕ =
    type-Prop is-strict-increasing-sequence-prop-ℕ

  is-prop-is-strict-increasing-sequence-ℕ :
    is-prop is-strict-increasing-sequence-ℕ
  is-prop-is-strict-increasing-sequence-ℕ =
    is-prop-type-Prop is-strict-increasing-sequence-prop-ℕ
```

### The type of strictly increasing sequences of natural numbers

```agda
strict-increasing-sequence-ℕ : UU lzero
strict-increasing-sequence-ℕ = type-subtype is-strict-increasing-sequence-prop-ℕ

module _
  (f : strict-increasing-sequence-ℕ)
  where

  sequence-strict-increasing-sequence-ℕ : sequence ℕ
  sequence-strict-increasing-sequence-ℕ = pr1 f

  is-strict-increasing-sequence-strict-increasing-sequence-ℕ :
    is-strict-increasing-sequence-ℕ
      sequence-strict-increasing-sequence-ℕ
  is-strict-increasing-sequence-strict-increasing-sequence-ℕ = pr2 f
```

### Strictly increasing values of a sequence of natural numbers

```agda
module _
  (f : sequence ℕ) (n : ℕ)
  where

  is-strict-increasing-value-prop-sequence-ℕ : Prop lzero
  is-strict-increasing-value-prop-sequence-ℕ = le-ℕ-Prop (f n) (f (succ-ℕ n))

  is-strict-increasing-value-sequence-ℕ : UU lzero
  is-strict-increasing-value-sequence-ℕ =
    type-Prop is-strict-increasing-value-prop-sequence-ℕ

  is-prop-is-strict-increasing-value-sequence-ℕ :
    is-prop is-strict-increasing-value-sequence-ℕ
  is-prop-is-strict-increasing-value-sequence-ℕ =
    is-prop-type-Prop is-strict-increasing-value-prop-sequence-ℕ
```

## Properties

### A sequence of natural numbers is strictly invceasing if and only if all its values are strictly increasing

```agda
module _
  (f : sequence ℕ)
  where

  strict-increasing-value-is-strict-increasing-sequence-ℕ :
    is-strict-increasing-sequence-ℕ f →
    ((n : ℕ) → is-strict-increasing-value-sequence-ℕ f n)
  strict-increasing-value-is-strict-increasing-sequence-ℕ H n =
    H n (succ-ℕ n) (succ-le-ℕ n)

  strict-increasing-is-strict-increasing-value-sequence-ℕ :
    ((n : ℕ) → is-strict-increasing-value-sequence-ℕ f n) →
    is-strict-increasing-sequence-ℕ f
  strict-increasing-is-strict-increasing-value-sequence-ℕ H p q I =
    based-ind-ℕ
      ( succ-ℕ p)
      ( λ k → le-ℕ (f p) (f k))
      ( H p)
      ( λ n J K → transitive-le-ℕ (f p) (f n) (f (succ-ℕ n)) K ((H n)))
      ( q)
      ( leq-succ-le-ℕ p q I)

module _
  (f : strict-increasing-sequence-ℕ)
  where

  strict-increasing-value-strict-increasing-sequence-ℕ :
    (n : ℕ) →
    is-strict-increasing-value-sequence-ℕ
      (sequence-strict-increasing-sequence-ℕ f)
      (n)
  strict-increasing-value-strict-increasing-sequence-ℕ =
    strict-increasing-value-is-strict-increasing-sequence-ℕ
      ( sequence-strict-increasing-sequence-ℕ f)
      ( is-strict-increasing-sequence-strict-increasing-sequence-ℕ f)
```

### Strictly increasing sequences of natural numbers preserve inequality

```agda
module _
  (f : strict-increasing-sequence-ℕ) (p q : ℕ)
  where

  preserves-leq-strict-increasing-sequence-ℕ :
    leq-ℕ p q →
    leq-ℕ
      (sequence-strict-increasing-sequence-ℕ f p)
      (sequence-strict-increasing-sequence-ℕ f q)
  preserves-leq-strict-increasing-sequence-ℕ =
    ( leq-eq-or-le-ℕ
      (sequence-strict-increasing-sequence-ℕ f p)
      (sequence-strict-increasing-sequence-ℕ f q)) ∘
    ( map-coproduct
      ( ap (sequence-strict-increasing-sequence-ℕ f))
      ( is-strict-increasing-sequence-strict-increasing-sequence-ℕ
        ( f)
        ( p)
        ( q))) ∘
    ( eq-or-le-leq-ℕ p q)
```

### The identity sequence is strictly increasing

```agda
is-strict-increasing-id-ℕ : is-strict-increasing-sequence-ℕ id
is-strict-increasing-id-ℕ i j = id

strict-increasing-id-ℕ : strict-increasing-sequence-ℕ
strict-increasing-id-ℕ = (id , is-strict-increasing-id-ℕ)
```

### The identity sequence is lesser than all strictly increasing sequences of natural numbers

```agda
module _
  (f : strict-increasing-sequence-ℕ)
  where

  leq-id-strict-increasing-sequence-ℕ :
    (n : ℕ) → leq-ℕ n (sequence-strict-increasing-sequence-ℕ f n)
  leq-id-strict-increasing-sequence-ℕ =
    ind-ℕ
      ( leq-zero-ℕ (sequence-strict-increasing-sequence-ℕ f zero-ℕ))
      ( λ n H →
        leq-succ-le-ℕ
          ( n)
          ( sequence-strict-increasing-sequence-ℕ f (succ-ℕ n))
          ( concatenate-leq-le-ℕ
            { n}
            { sequence-strict-increasing-sequence-ℕ f n}
            { sequence-strict-increasing-sequence-ℕ f (succ-ℕ n)}
            ( H)
            ( is-strict-increasing-sequence-strict-increasing-sequence-ℕ
              ( f)
              ( n)
              ( succ-ℕ n)
              ( succ-le-ℕ n))))
```

### The successor function is strictly increasing

```agda
is-strict-increasing-succ-ℕ : is-strict-increasing-sequence-ℕ succ-ℕ
is-strict-increasing-succ-ℕ i j H = H

strict-increasing-succ-ℕ : strict-increasing-sequence-ℕ
strict-increasing-succ-ℕ = (succ-ℕ , is-strict-increasing-succ-ℕ)
```

### The composition of strictly increasing sequences of natural numbers is strictly increasing

```agda
module _
  (g f : sequence ℕ)
  (G : is-strict-increasing-sequence-ℕ g)
  (F : is-strict-increasing-sequence-ℕ f)
  where

  is-strict-increasing-comp-is-strict-increasing-sequence-ℕ :
    is-strict-increasing-sequence-ℕ (g ∘ f)
  is-strict-increasing-comp-is-strict-increasing-sequence-ℕ p q =
    G (f p) (f q) ∘ (F p q)

comp-strict-increasing-sequence-ℕ :
  strict-increasing-sequence-ℕ →
  strict-increasing-sequence-ℕ →
  strict-increasing-sequence-ℕ
comp-strict-increasing-sequence-ℕ g f =
  ( ( sequence-strict-increasing-sequence-ℕ g) ∘
    ( sequence-strict-increasing-sequence-ℕ f)) ,
  ( is-strict-increasing-comp-is-strict-increasing-sequence-ℕ
    ( sequence-strict-increasing-sequence-ℕ g)
    ( sequence-strict-increasing-sequence-ℕ f)
    ( is-strict-increasing-sequence-strict-increasing-sequence-ℕ g)
    ( is-strict-increasing-sequence-strict-increasing-sequence-ℕ f))
```

### A strictly increasing sequence of natural numbers takes arbitrarily large values

```agda
module _
  (f : strict-increasing-sequence-ℕ) (M : ℕ)
  where

  unbounded-strict-increasing-sequence-ℕ :
    Σ ℕ (λ n → leq-ℕ M (sequence-strict-increasing-sequence-ℕ f n))
  unbounded-strict-increasing-sequence-ℕ =
    (M , leq-id-strict-increasing-sequence-ℕ f M)

  modulus-unbounded-strict-increasing-sequence-ℕ : ℕ
  modulus-unbounded-strict-increasing-sequence-ℕ =
    pr1 unbounded-strict-increasing-sequence-ℕ

  value-unbounded-strict-increasing-sequence-ℕ : ℕ
  value-unbounded-strict-increasing-sequence-ℕ =
    sequence-strict-increasing-sequence-ℕ f
      modulus-unbounded-strict-increasing-sequence-ℕ

  is-modulus-unbounded-strict-increasing-sequence-ℕ :
    leq-ℕ M value-unbounded-strict-increasing-sequence-ℕ
  is-modulus-unbounded-strict-increasing-sequence-ℕ =
    pr2 unbounded-strict-increasing-sequence-ℕ

  is-∞-modulus-unbounded-strict-increasing-sequence-ℕ :
    (p : ℕ) →
    leq-ℕ modulus-unbounded-strict-increasing-sequence-ℕ p →
    leq-ℕ M (sequence-strict-increasing-sequence-ℕ f p)
  is-∞-modulus-unbounded-strict-increasing-sequence-ℕ =
    based-ind-ℕ
      ( modulus-unbounded-strict-increasing-sequence-ℕ)
      ( λ k → leq-ℕ M (sequence-strict-increasing-sequence-ℕ f k))
      ( is-modulus-unbounded-strict-increasing-sequence-ℕ)
      ( λ n I →
        transitive-leq-ℕ
          ( M)
          ( sequence-strict-increasing-sequence-ℕ f n)
          ( sequence-strict-increasing-sequence-ℕ f (succ-ℕ n))
          ( leq-le-ℕ
            ( sequence-strict-increasing-sequence-ℕ f n)
            ( sequence-strict-increasing-sequence-ℕ f (succ-ℕ n))
            ( strict-increasing-value-strict-increasing-sequence-ℕ f n)))
```

### The strictly increasing sequence of natural numbers that skips the `n + 1` first terms

```agda
skip-ℕ : ℕ → ℕ → ℕ
skip-ℕ n m = succ-ℕ (n +ℕ m)

is-strict-increasing-skip-ℕ :
  (n : ℕ) → is-strict-increasing-sequence-ℕ (skip-ℕ n)
is-strict-increasing-skip-ℕ n p q I =
  concatenate-le-leq-ℕ
    { add-ℕ n p}
    { succ-ℕ (add-ℕ n p)}
    { add-ℕ n q}
    ( succ-le-ℕ (add-ℕ n p))
    ( preserves-leq-right-add-ℕ n (succ-ℕ p) q (leq-succ-le-ℕ p q I))

strict-increasing-skip-ℕ : (n : ℕ) → strict-increasing-sequence-ℕ
strict-increasing-skip-ℕ n = (skip-ℕ n , is-strict-increasing-skip-ℕ n)

associative-skip-ℕ : (i j k : ℕ) →
  skip-ℕ (skip-ℕ i j) k ＝ skip-ℕ i (skip-ℕ j k)
associative-skip-ℕ i j k =
  ap
    ( succ-ℕ)
    ( ( left-successor-law-add-ℕ (i +ℕ j) k) ∙
      ( ap succ-ℕ (associative-add-ℕ i j k)))

le-skip-ℕ : (m n : ℕ) → le-ℕ m (skip-ℕ m n)
le-skip-ℕ m n = le-succ-leq-ℕ m (m +ℕ n) (leq-add-ℕ m n)

le-skip-ℕ' : (m n : ℕ) → le-ℕ m (skip-ℕ n m)
le-skip-ℕ' m n = le-succ-leq-ℕ m (n +ℕ m) (leq-add-ℕ' m n)
```
