# Monotonic sequences of natural numbers

```agda
module elementary-number-theory.monotonic-sequences-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.asymptotical-dependent-sequences
open import foundation.constant-sequences
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sequences
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

Monotic sequences of natural numbers are functions `f : ℕ → ℕ` that preserve or
reverse (strict) inequality of natural numbers.

## Definitions

### Increasing sequences of natural numbers

```agda
module _
  (f : sequence ℕ)
  where

  is-increasing-prop-sequence-ℕ : Prop lzero
  is-increasing-prop-sequence-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (leq-ℕ-Prop i j) (leq-ℕ-Prop (f i) (f j))))

  is-increasing-sequence-ℕ : UU lzero
  is-increasing-sequence-ℕ =
    type-Prop is-increasing-prop-sequence-ℕ

  is-prop-is-increasing-sequence-ℕ :
    is-prop is-increasing-sequence-ℕ
  is-prop-is-increasing-sequence-ℕ =
    is-prop-type-Prop is-increasing-prop-sequence-ℕ
```

### Strictly increasing sequences of natural numbers

```agda
module _
  (f : sequence ℕ)
  where

  is-strictly-increasing-sequence-prop-ℕ : Prop lzero
  is-strictly-increasing-sequence-prop-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (le-ℕ-Prop i j) (le-ℕ-Prop (f i) (f j))))

  is-strictly-increasing-sequence-ℕ : UU lzero
  is-strictly-increasing-sequence-ℕ =
    type-Prop is-strictly-increasing-sequence-prop-ℕ

  is-prop-is-strictly-increasing-sequence-ℕ :
    is-prop is-strictly-increasing-sequence-ℕ
  is-prop-is-strictly-increasing-sequence-ℕ =
    is-prop-type-Prop is-strictly-increasing-sequence-prop-ℕ
```

### Decreasing sequences of natural numbers

```agda
module _
  (f : sequence ℕ)
  where

  is-decreasing-sequence-prop-ℕ : Prop lzero
  is-decreasing-sequence-prop-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (leq-ℕ-Prop i j) (leq-ℕ-Prop (f j) (f i))))

  is-decreasing-sequence-ℕ : UU lzero
  is-decreasing-sequence-ℕ = type-Prop is-decreasing-sequence-prop-ℕ

  is-prop-is-decreasing-sequence-ℕ : is-prop is-decreasing-sequence-ℕ
  is-prop-is-decreasing-sequence-ℕ =
    is-prop-type-Prop is-decreasing-sequence-prop-ℕ
```

### Strictly decreasing sequences of natural numbers

```agda
module _
  (f : sequence ℕ)
  where

  is-strictly-decreasing-sequence-prop-ℕ : Prop lzero
  is-strictly-decreasing-sequence-prop-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (le-ℕ-Prop i j) (le-ℕ-Prop (f j) (f i))))

  is-strictly-decreasing-sequence-ℕ : UU lzero
  is-strictly-decreasing-sequence-ℕ =
    type-Prop is-strictly-decreasing-sequence-prop-ℕ

  is-prop-is-strictly-decreasing-sequence-ℕ :
    is-prop is-strictly-decreasing-sequence-ℕ
  is-prop-is-strictly-decreasing-sequence-ℕ =
    is-prop-type-Prop is-strictly-decreasing-sequence-prop-ℕ
```

### Monotonic values of sequences of natural numbers

```agda
module _
  (f : sequence ℕ) (n : ℕ)
  where

  is-increasing-value-prop-sequence-ℕ : Prop lzero
  is-increasing-value-prop-sequence-ℕ = leq-ℕ-Prop (f n) (f (succ-ℕ n))

  is-increasing-value-sequence-ℕ : UU lzero
  is-increasing-value-sequence-ℕ =
    type-Prop is-increasing-value-prop-sequence-ℕ

  is-prop-is-increasing-value-sequence-ℕ :
    is-prop is-increasing-value-sequence-ℕ
  is-prop-is-increasing-value-sequence-ℕ =
    is-prop-type-Prop is-increasing-value-prop-sequence-ℕ

  is-decreasing-value-prop-sequence-ℕ : Prop lzero
  is-decreasing-value-prop-sequence-ℕ = leq-ℕ-Prop (f (succ-ℕ n)) (f n)

  is-decreasing-value-sequence-ℕ : UU lzero
  is-decreasing-value-sequence-ℕ =
    type-Prop is-decreasing-value-prop-sequence-ℕ

  is-prop-is-decreasing-value-sequence-ℕ :
    is-prop is-decreasing-value-sequence-ℕ
  is-prop-is-decreasing-value-sequence-ℕ =
    is-prop-type-Prop is-decreasing-value-prop-sequence-ℕ
```

### Strict monotonic values of sequences of natural numbers

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

  is-strict-decreasing-value-prop-sequence-ℕ : Prop lzero
  is-strict-decreasing-value-prop-sequence-ℕ = le-ℕ-Prop (f (succ-ℕ n)) (f n)

  is-strict-decreasing-value-sequence-ℕ : UU lzero
  is-strict-decreasing-value-sequence-ℕ =
    type-Prop is-strict-decreasing-value-prop-sequence-ℕ

  is-prop-is-strict-decreasing-value-sequence-ℕ :
    is-prop is-strict-decreasing-value-sequence-ℕ
  is-prop-is-strict-decreasing-value-sequence-ℕ =
    is-prop-type-Prop is-strict-decreasing-value-prop-sequence-ℕ
```

## Properties

### A sequence is monotonic if and only if all its values are monotonic of the same monotonicity

```agda
module _
  (f : sequence ℕ)
  where

  is-increasing-value-is-increasing-sequence-ℕ :
    is-increasing-sequence-ℕ f →
    ((n : ℕ) → is-increasing-value-sequence-ℕ f n)
  is-increasing-value-is-increasing-sequence-ℕ H n =
    H n (succ-ℕ n) (succ-leq-ℕ n)

  is-increasing-is-increasing-value-sequence-ℕ :
    ((n : ℕ) → is-increasing-value-sequence-ℕ f n) →
    is-increasing-sequence-ℕ f
  is-increasing-is-increasing-value-sequence-ℕ H p =
    based-ind-ℕ
      ( p)
      ( λ k → leq-ℕ (f p) (f k))
      ( refl-leq-ℕ (f p))
      ( λ n J → transitive-leq-ℕ (f p) (f n) (f (succ-ℕ n)) (H n))

  is-decreasing-value-is-decreasing-sequence-ℕ :
    is-decreasing-sequence-ℕ f →
    ((n : ℕ) → is-decreasing-value-sequence-ℕ f n)
  is-decreasing-value-is-decreasing-sequence-ℕ H n =
    H n (succ-ℕ n) (succ-leq-ℕ n)

  is-decreasing-is-decreasing-value-sequence-ℕ :
    ((n : ℕ) → is-decreasing-value-sequence-ℕ f n) →
    is-decreasing-sequence-ℕ f
  is-decreasing-is-decreasing-value-sequence-ℕ H p =
    based-ind-ℕ
      ( p)
      ( λ k → leq-ℕ (f k) (f p))
      ( refl-leq-ℕ (f p))
      ( λ n J K → transitive-leq-ℕ (f (succ-ℕ n)) (f n) (f p) K (H n))
```

### A sequence is strictly monotonic if and only if all its values are strictly monotonic with the same monotonicity

```agda
module _
  (f : sequence ℕ)
  where

  is-strict-increasing-value-is-strictly-increasing-sequence-ℕ :
    is-strictly-increasing-sequence-ℕ f →
    ((n : ℕ) → is-strict-increasing-value-sequence-ℕ f n)
  is-strict-increasing-value-is-strictly-increasing-sequence-ℕ H n =
    H n (succ-ℕ n) (succ-le-ℕ n)

  is-strictly-increasing-is-strict-increasing-value-sequence-ℕ :
    ((n : ℕ) → is-strict-increasing-value-sequence-ℕ f n) →
    is-strictly-increasing-sequence-ℕ f
  is-strictly-increasing-is-strict-increasing-value-sequence-ℕ H p q I =
    based-ind-ℕ
      ( succ-ℕ p)
      ( λ k → le-ℕ (f p) (f k))
      ( H p)
      ( λ n J K → transitive-le-ℕ (f p) (f n) (f (succ-ℕ n)) K ((H n)))
      ( q)
      ( leq-succ-le-ℕ p q I)

  is-strict-decreasing-value-is-strictly-decreasing-sequence-ℕ :
    is-strictly-decreasing-sequence-ℕ f →
    ((n : ℕ) → is-strict-decreasing-value-sequence-ℕ f n)
  is-strict-decreasing-value-is-strictly-decreasing-sequence-ℕ H n =
    H n (succ-ℕ n) (succ-le-ℕ n)

  is-strictly-decreasing-is-strict-decreasing-value-sequence-ℕ :
    ((n : ℕ) → is-strict-decreasing-value-sequence-ℕ f n) →
    is-strictly-decreasing-sequence-ℕ f
  is-strictly-decreasing-is-strict-decreasing-value-sequence-ℕ H p q I =
    based-ind-ℕ
      ( succ-ℕ p)
      ( λ k → le-ℕ (f k) (f p))
      ( H p)
      ( λ n J → transitive-le-ℕ (f (succ-ℕ n)) (f n) (f p) (H n))
      ( q)
      ( leq-succ-le-ℕ p q I)
```

## Strictly monotonic sequences of natural numbers are monotonic

```agda
module _
  (f : sequence ℕ)
  where

  is-increasing-value-is-strict-increasing-value-sequence-ℕ :
    (n : ℕ) →
    is-strict-increasing-value-sequence-ℕ f n →
    is-increasing-value-sequence-ℕ f n
  is-increasing-value-is-strict-increasing-value-sequence-ℕ n =
    leq-le-ℕ (f n) (f (succ-ℕ n))

  is-increasing-is-strictly-increasing-sequence-ℕ :
    is-strictly-increasing-sequence-ℕ f → is-increasing-sequence-ℕ f
  is-increasing-is-strictly-increasing-sequence-ℕ H =
    is-increasing-is-increasing-value-sequence-ℕ f
      ( λ n → is-increasing-value-is-strict-increasing-value-sequence-ℕ n
        ( is-strict-increasing-value-is-strictly-increasing-sequence-ℕ f H n))
```

### A monotonic value is either stationnary or strictly monotonic

```agda
module _
  (f : sequence ℕ) (n : ℕ)
  where

  decide-is-stationnary-is-increasing-value-sequence-ℕ :
    is-increasing-value-sequence-ℕ f n →
    (is-stationnary-value-sequence f n) +
    (is-strict-increasing-value-sequence-ℕ f n)
  decide-is-stationnary-is-increasing-value-sequence-ℕ =
    eq-or-le-leq-ℕ (f n) (f (succ-ℕ n))

  decide-is-stationnary-is-decreasing-value-sequence-ℕ :
    is-decreasing-value-sequence-ℕ f n →
    (is-stationnary-value-sequence f n) +
    (is-strict-decreasing-value-sequence-ℕ f n)
  decide-is-stationnary-is-decreasing-value-sequence-ℕ H =
    map-coproduct inv id (eq-or-le-leq-ℕ (f (succ-ℕ n)) (f n) H)
```

### A decreasing sequence that takes the value zero is asymptotically equal to zero

```agda
module _
  (f : sequence ℕ) (H : is-decreasing-sequence-ℕ f)
  where

  is-∞-zero-is-zero-value-decreasing-sequence-ℕ :
    (n : ℕ) (K : f n ＝ zero-ℕ) → (k : ℕ) → leq-ℕ n k → zero-ℕ ＝ f k
  is-∞-zero-is-zero-value-decreasing-sequence-ℕ n K k I =
    is-zero-leq-zero-ℕ' (f k) (tr (leq-ℕ (f k)) K (H n k I))
```

### A decreasing sequence of natural numbers that has no strictly decreasing value is constant

```agda
module _
  (f : sequence ℕ) (H : is-decreasing-sequence-ℕ f)
  where

  is-constant-no-strict-decreasing-value-decreasing-sequence-ℕ :
    ((n : ℕ) → ¬ (is-strict-decreasing-value-sequence-ℕ f n)) →
    is-constant-sequence f
  is-constant-no-strict-decreasing-value-decreasing-sequence-ℕ K =
    is-constant-is-stationnary-value-sequence f
      ( λ n →
        rec-coproduct
          ( id)
          ( ex-falso ∘ (K n))
          ( decide-is-stationnary-is-decreasing-value-sequence-ℕ f n
            ( is-decreasing-value-is-decreasing-sequence-ℕ f H n)))
```

### A decreasing sequence of natural numbers that asymptotically has no strictly decreasing value is asymptotically constant

```agda
module _
  (f : sequence ℕ) (H : is-decreasing-sequence-ℕ f) (N : ℕ)
  where

  is-∞-constant-∞-no-strict-decreasing-value-decreasing-sequence-ℕ :
    ((n : ℕ) → (leq-ℕ N n) → ¬ (is-strict-decreasing-value-sequence-ℕ f n)) →
    ((n : ℕ) → leq-ℕ N n → f N ＝ f n)
  is-∞-constant-∞-no-strict-decreasing-value-decreasing-sequence-ℕ K =
    based-ind-ℕ
      ( N)
      ( λ n → f N ＝ f n)
      ( refl)
      ( λ n I J →
        rec-coproduct
          ( J ∙_)
          ( ex-falso ∘ (K n I))
          ( decide-is-stationnary-is-decreasing-value-sequence-ℕ f n
            (is-decreasing-value-is-decreasing-sequence-ℕ f H n)))
```

### A decreasing sequence of natural numbers with bounded strictly decreasing values is asymptotically constant

```agda
module _
  (f : sequence ℕ) (H : is-decreasing-sequence-ℕ f) (N : ℕ)
  where

  is-∞-constant-is-bounded-strict-decreasing-value-decreasing-sequence-ℕ :
    ((n : ℕ) → is-strict-decreasing-value-sequence-ℕ f n → le-ℕ n N) →
    ((n : ℕ) → leq-ℕ N n → f N ＝ f n)
  is-∞-constant-is-bounded-strict-decreasing-value-decreasing-sequence-ℕ K =
    is-∞-constant-∞-no-strict-decreasing-value-decreasing-sequence-ℕ f H N
      ( λ n I J → contradiction-le-ℕ n N (K n J) I)
```

### Any subsequence of a decreasing sequence of natural numbers is decreasing

```agda
module _
  (f : sequence ℕ) (H : is-decreasing-sequence-ℕ f)
  (φ : sequence ℕ) (K : is-strictly-increasing-sequence-ℕ φ)
  where

  is-decreasing-subsequence-decreasing-sequence-ℕ :
    is-decreasing-sequence-ℕ (f ∘ φ)
  is-decreasing-subsequence-decreasing-sequence-ℕ p q I =
    H
      ( φ p)
      ( φ q)
      ( is-increasing-is-strictly-increasing-sequence-ℕ φ K p q I)
```

### There exist no strictly decreasing sequences of natural numbers

```agda
no-strictly-decreasing-sequence-leq-ℕ :
  (f : sequence ℕ) →
  (N : ℕ) →
  is-strictly-decreasing-sequence-ℕ f →
  leq-ℕ (f zero-ℕ) N →
  empty
no-strictly-decreasing-sequence-leq-ℕ f zero-ℕ H =
  concatenate-le-leq-ℕ
    { f 1}
    { f 0}
    { 0}
    ( H 0 1 (succ-le-ℕ 0))
no-strictly-decreasing-sequence-leq-ℕ f (succ-ℕ N) H K =
  no-strictly-decreasing-sequence-leq-ℕ
    ( f ∘ succ-ℕ)
    ( N)
    ( λ i j → H (succ-ℕ i) (succ-ℕ j))
    ( leq-le-succ-ℕ
      ( f 1)
      ( N)
      ( concatenate-le-leq-ℕ
        { f 1}
        { f 0}
        { succ-ℕ N}
        ( H 0 1 (succ-le-ℕ 0))
        ( K)))

no-strictly-decreasing-sequence-ℕ :
  (f : sequence ℕ) → ¬ (is-strictly-decreasing-sequence-ℕ f)
no-strictly-decreasing-sequence-ℕ f H =
  no-strictly-decreasing-sequence-leq-ℕ f (f 0) H (refl-leq-ℕ (f 0))
```

### Strictly increasing sequences of natural numbers grow infinitely

```agda
module _
  (f : sequence ℕ) (H : is-strictly-increasing-sequence-ℕ f)
  where

  limit-∞-is-strictly-increasing-sequence-ℕ :
    (M : ℕ) → asymptotically (λ n → leq-ℕ M (f n))
  limit-∞-is-strictly-increasing-sequence-ℕ zero-ℕ =
    ( zero-ℕ , λ n K → leq-zero-ℕ (f n))
  limit-∞-is-strictly-increasing-sequence-ℕ (succ-ℕ M) =
    map-Σ
      ( is-modulus-dependent-sequence (λ n → leq-ℕ (succ-ℕ M) (f n)))
      ( succ-ℕ)
      ( λ N K n I →
        leq-succ-le-ℕ M (f n)
          (concatenate-leq-le-ℕ
            { M}
            { f N}
            { f n}
            ( K N (refl-leq-ℕ N))
            ( H N n
              ( concatenate-le-leq-ℕ
                { N}
                { succ-ℕ N}
                { n}
                ( succ-le-ℕ N)
                ( I)))))
      ( limit-∞-is-strictly-increasing-sequence-ℕ M)

  modulus-limit-∞-is-strictly-increasing-sequence-ℕ : ℕ → ℕ
  modulus-limit-∞-is-strictly-increasing-sequence-ℕ M =
    pr1 (limit-∞-is-strictly-increasing-sequence-ℕ M)

  is-modulus-limit-∞-is-strictly-increasing-sequence-ℕ :
    (M p : ℕ) →
    leq-ℕ (modulus-limit-∞-is-strictly-increasing-sequence-ℕ M) p →
    leq-ℕ M (f p)
  is-modulus-limit-∞-is-strictly-increasing-sequence-ℕ M =
    pr2 (limit-∞-is-strictly-increasing-sequence-ℕ M)
```
