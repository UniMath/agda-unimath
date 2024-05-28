# Strictly monotonic sequences of natural numbers

```agda
module elementary-number-theory.strict-monotonic-sequences-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.asymptotical-dependent-sequences
open import foundation.cartesian-product-types
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
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

Strictly monotic sequences of natural numbers are functions `f : ℕ → ℕ` that
preserve or reverse strict inequality of natural numbers.

Strictly decreasing sequences of natural numbers don't exist.

Strictly increasing sequences of natural numbers are stable under composition
and can get arbitrarily large.

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

### Strictly decreasing sequences of natural numbers

```agda
module _
  (f : sequence ℕ)
  where

  is-strict-decreasing-sequence-prop-ℕ : Prop lzero
  is-strict-decreasing-sequence-prop-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (le-ℕ-Prop i j) (le-ℕ-Prop (f j) (f i))))

  is-strict-decreasing-sequence-ℕ : UU lzero
  is-strict-decreasing-sequence-ℕ =
    type-Prop is-strict-decreasing-sequence-prop-ℕ

  is-prop-is-strict-decreasing-sequence-ℕ :
    is-prop is-strict-decreasing-sequence-ℕ
  is-prop-is-strict-decreasing-sequence-ℕ =
    is-prop-type-Prop is-strict-decreasing-sequence-prop-ℕ
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

### A sequence is strictly monotonic if and only if all its values are strictly monotonic with the same monotonicity

```agda
module _
  (f : sequence ℕ)
  where

  is-strict-increasing-value-is-strict-increasing-sequence-ℕ :
    is-strict-increasing-sequence-ℕ f →
    ((n : ℕ) → is-strict-increasing-value-sequence-ℕ f n)
  is-strict-increasing-value-is-strict-increasing-sequence-ℕ H n =
    H n (succ-ℕ n) (succ-le-ℕ n)

  is-strict-increasing-is-strict-increasing-value-sequence-ℕ :
    ((n : ℕ) → is-strict-increasing-value-sequence-ℕ f n) →
    is-strict-increasing-sequence-ℕ f
  is-strict-increasing-is-strict-increasing-value-sequence-ℕ H p q I =
    based-ind-ℕ
      ( succ-ℕ p)
      ( λ k → le-ℕ (f p) (f k))
      ( H p)
      ( λ n J K → transitive-le-ℕ (f p) (f n) (f (succ-ℕ n)) K ((H n)))
      ( q)
      ( leq-succ-le-ℕ p q I)

  is-strict-decreasing-value-is-strict-decreasing-sequence-ℕ :
    is-strict-decreasing-sequence-ℕ f →
    ((n : ℕ) → is-strict-decreasing-value-sequence-ℕ f n)
  is-strict-decreasing-value-is-strict-decreasing-sequence-ℕ H n =
    H n (succ-ℕ n) (succ-le-ℕ n)

  is-strict-decreasing-is-strict-decreasing-value-sequence-ℕ :
    ((n : ℕ) → is-strict-decreasing-value-sequence-ℕ f n) →
    is-strict-decreasing-sequence-ℕ f
  is-strict-decreasing-is-strict-decreasing-value-sequence-ℕ H p q I =
    based-ind-ℕ
      ( succ-ℕ p)
      ( λ k → le-ℕ (f k) (f p))
      ( H p)
      ( λ n J → transitive-le-ℕ (f (succ-ℕ n)) (f n) (f p) (H n))
      ( q)
      ( leq-succ-le-ℕ p q I)
```

### There exist no strictly decreasing sequences of natural numbers

```agda
no-strict-decreasing-sequence-leq-ℕ :
  (f : sequence ℕ) →
  (N : ℕ) →
  is-strict-decreasing-sequence-ℕ f →
  leq-ℕ (f zero-ℕ) N →
  empty
no-strict-decreasing-sequence-leq-ℕ f zero-ℕ H =
  concatenate-le-leq-ℕ
    { f 1}
    { f 0}
    { 0}
    ( H 0 1 (succ-le-ℕ 0))
no-strict-decreasing-sequence-leq-ℕ f (succ-ℕ N) H K =
  no-strict-decreasing-sequence-leq-ℕ
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

module _
  (f : sequence ℕ)
  where

  no-strict-decreasing-sequence-ℕ : ¬ (is-strict-decreasing-sequence-ℕ f)
  no-strict-decreasing-sequence-ℕ H =
    no-strict-decreasing-sequence-leq-ℕ f (f 0) H (refl-leq-ℕ (f 0))

  no-strict-decreasing-value-sequence-ℕ :
    ¬ ((n : ℕ) → is-strict-decreasing-value-sequence-ℕ f n)
  no-strict-decreasing-value-sequence-ℕ =
    ( no-strict-decreasing-sequence-ℕ) ∘
    ( is-strict-decreasing-is-strict-decreasing-value-sequence-ℕ f)
```

### The identity sequence is strictly increasing

```agda
is-strict-increasing-id-ℕ : is-strict-increasing-sequence-ℕ id
is-strict-increasing-id-ℕ i j = id

strict-increasing-id-ℕ : strict-increasing-sequence-ℕ
strict-increasing-id-ℕ = id , is-strict-increasing-id-ℕ
```

### The successor function is strictly increasing

```agda
is-strict-increasing-succ-ℕ : is-strict-increasing-sequence-ℕ succ-ℕ
is-strict-increasing-succ-ℕ i j H = H

strict-increasing-succ-ℕ : strict-increasing-sequence-ℕ
strict-increasing-succ-ℕ = (succ-ℕ , is-strict-increasing-succ-ℕ)
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
  (f : sequence ℕ) (H : is-strict-increasing-sequence-ℕ f)
  where

  limit-∞-is-strict-increasing-sequence-ℕ :
    (M : ℕ) → asymptotically (λ n → leq-ℕ M (f n))
  limit-∞-is-strict-increasing-sequence-ℕ zero-ℕ =
    ( zero-ℕ , λ n K → leq-zero-ℕ (f n))
  limit-∞-is-strict-increasing-sequence-ℕ (succ-ℕ M) =
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
      ( limit-∞-is-strict-increasing-sequence-ℕ M)

  modulus-limit-∞-is-strict-increasing-sequence-ℕ : ℕ → ℕ
  modulus-limit-∞-is-strict-increasing-sequence-ℕ M =
    pr1 (limit-∞-is-strict-increasing-sequence-ℕ M)

  is-modulus-limit-∞-is-strict-increasing-sequence-ℕ :
    (M p : ℕ) →
    leq-ℕ (modulus-limit-∞-is-strict-increasing-sequence-ℕ M) p →
    leq-ℕ M (f p)
  is-modulus-limit-∞-is-strict-increasing-sequence-ℕ M =
    pr2 (limit-∞-is-strict-increasing-sequence-ℕ M)
```
