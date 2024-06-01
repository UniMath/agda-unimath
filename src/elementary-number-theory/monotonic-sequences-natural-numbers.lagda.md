# Monotonic sequences of natural numbers

```agda
module elementary-number-theory.monotonic-sequences-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strict-monotonic-sequences-natural-numbers

open import foundation.asymptotical-dependent-sequences
open import foundation.asymptotically-constant-sequences
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
open import foundation.subsequences
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels

open import order-theory.monotonic-sequences-posets
```

</details>

## Idea

Monotonic sequences of natural numbers are functions `f : ℕ → ℕ` that preserve
or reverse inequality of natural numbers.

## Definitions

### Monotonic values of sequences of natural numbers

```agda
module _
  (f : sequence ℕ) (n : ℕ)
  where

  is-increasing-value-sequence-ℕ : UU lzero
  is-increasing-value-sequence-ℕ =
    is-increasing-value-sequence-poset ℕ-Poset f n

  is-decreasing-value-sequence-ℕ : UU lzero
  is-decreasing-value-sequence-ℕ =
    is-decreasing-value-sequence-poset ℕ-Poset f n
```

### Monotonic sequences of natural numbers

```agda
module _
  (f : sequence ℕ)
  where

  is-increasing-sequence-ℕ : UU lzero
  is-increasing-sequence-ℕ = is-increasing-sequence-poset ℕ-Poset f

  is-decreasing-sequence-ℕ : UU lzero
  is-decreasing-sequence-ℕ = is-decreasing-sequence-poset ℕ-Poset f
```

## Properties

### A decreasing sequence of natural numbers that takes the value zero is asymptotically equal to zero

```agda
module _
  {f : sequence ℕ} (H : is-decreasing-sequence-ℕ f)
  where

  eq-∞-zero-is-zero-value-decreasing-sequence-ℕ :
    Σ ℕ (λ n → zero-ℕ ＝ f n) → asymptotically (λ n → zero-ℕ ＝ f n)
  eq-∞-zero-is-zero-value-decreasing-sequence-ℕ =
    tot
      ( λ n K k I →
        is-zero-leq-zero-ℕ'
          ( f k)
          ( inv-tr (leq-ℕ (f k)) K (H n k I)))
```

### A monotonic value of a sequence of natural numbers is either stationnary or strictly monotonic

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

### Any value of a monotonic sequence of natural numbers that is not a strict value is stationnary

```agda
module _
  (f : sequence ℕ)
  where

  stationnary-value-is-not-strict-value-increasing-sequence-ℕ :
    is-increasing-sequence-ℕ f →
    (n : ℕ) →
    ¬ (is-strict-increasing-value-sequence-ℕ f n) →
    is-stationnary-value-sequence f n
  stationnary-value-is-not-strict-value-increasing-sequence-ℕ H n K =
    map-right-unit-law-coproduct-is-empty
      ( is-stationnary-value-sequence f n)
      ( is-strict-increasing-value-sequence-ℕ f n)
      ( K)
      ( decide-is-stationnary-is-increasing-value-sequence-ℕ
        ( f)
        ( n)
        ( increasing-value-is-increasing-sequence-poset ℕ-Poset {f} H n))

  stationnary-value-is-not-strict-value-decreasing-sequence-ℕ :
    is-decreasing-sequence-ℕ f →
    (n : ℕ) →
    ¬ (is-strict-decreasing-value-sequence-ℕ f n) →
    is-stationnary-value-sequence f n
  stationnary-value-is-not-strict-value-decreasing-sequence-ℕ H n K =
    map-right-unit-law-coproduct-is-empty
      ( is-stationnary-value-sequence f n)
      ( is-strict-decreasing-value-sequence-ℕ f n)
      ( K)
      ( decide-is-stationnary-is-decreasing-value-sequence-ℕ
        ( f)
        ( n)
        ( decreasing-value-is-decreasing-sequence-poset ℕ-Poset {f} H n))
```

### A decreasing sequence of natural numbers that has no strictly decreasing value is constant

```agda
module _
  {f : sequence ℕ} (H : is-decreasing-sequence-ℕ f)
  where

  constant-no-strict-decreasing-value-decreasing-sequence-ℕ :
    ((n : ℕ) → ¬ (is-strict-decreasing-value-sequence-ℕ f n)) →
    is-constant-sequence f
  constant-no-strict-decreasing-value-decreasing-sequence-ℕ K =
    is-constant-is-stationnary-value-sequence f
      ( λ n →
        stationnary-value-is-not-strict-value-decreasing-sequence-ℕ
          ( f)
          ( H)
          ( n)
          ( K n))
```

### A decreasing sequence of natural numbers that asymptotically has no strictly decreasing value is asymptotically constant

```agda
module _
  {f : sequence ℕ} (H : is-decreasing-sequence-ℕ f)
  where

  ∞-constant-∞-no-strict-value-decreasing-sequence-ℕ :
    asymptotically (λ n → ¬ (is-strict-decreasing-value-sequence-ℕ f n)) →
    is-∞-constant-sequence f
  ∞-constant-∞-no-strict-value-decreasing-sequence-ℕ =
    ( is-∞-constant-is-∞-stationnary-sequence f) ∘
    ( map-asymptotically-Π
      ( stationnary-value-is-not-strict-value-decreasing-sequence-ℕ f H))
```

### A decreasing sequence of natural numbers with bounded strictly decreasing values is asymptotically constant

```agda
module _
  (f : sequence ℕ) (N : ℕ)
  where

  is-upper-bound-strict-decreasing-value-sequence-ℕ : UU lzero
  is-upper-bound-strict-decreasing-value-sequence-ℕ =
    (n : ℕ) → is-strict-decreasing-value-sequence-ℕ f n → le-ℕ n N

module _
  {f : sequence ℕ} (H : is-decreasing-sequence-ℕ f)
  where

  ∞-constant-is-upper-bounded-strict-value-decreasing-sequence-ℕ :
    Σ ℕ (is-upper-bound-strict-decreasing-value-sequence-ℕ f) →
    is-∞-constant-sequence f
  ∞-constant-is-upper-bounded-strict-value-decreasing-sequence-ℕ =
    ( ∞-constant-∞-no-strict-value-decreasing-sequence-ℕ H) ∘
    ( rec-Σ (λ N I → (N , (λ n J L → contradiction-le-ℕ n N (I n L) J))))
```

### Asymptotical strictly decreasing values

```agda
module _
  (f : sequence ℕ) (N n : ℕ)
  where

  is-∞-strict-decreasing-value-prop-sequence-ℕ : Prop lzero
  is-∞-strict-decreasing-value-prop-sequence-ℕ =
    product-Prop
      (leq-ℕ-Prop N n)
      (is-strict-decreasing-value-prop-sequence-ℕ f n)

  is-∞-strict-decreasing-value-sequence-ℕ : UU lzero
  is-∞-strict-decreasing-value-sequence-ℕ =
    type-Prop is-∞-strict-decreasing-value-prop-sequence-ℕ

  is-prop-is-∞-strict-decreasing-value-sequence-ℕ :
    is-prop is-∞-strict-decreasing-value-sequence-ℕ
  is-prop-is-∞-strict-decreasing-value-sequence-ℕ =
    is-prop-type-Prop is-∞-strict-decreasing-value-prop-sequence-ℕ
```

### A decreasing sequence of natural numbers with no asymptotical strictly decreasing values is asymptotically constant

```agda
module _
  {f : sequence ℕ} (H : is-decreasing-sequence-ℕ f)
  where

  ∞-constant-no-∞-strict-decreasing-value-decreasing-sequence-ℕ :
    Σ ℕ (λ N → ¬ Σ ℕ (is-∞-strict-decreasing-value-sequence-ℕ f N)) →
    is-∞-constant-sequence f
  ∞-constant-no-∞-strict-decreasing-value-decreasing-sequence-ℕ =
    ( ∞-constant-∞-no-strict-value-decreasing-sequence-ℕ H) ∘
    ( tot (λ n K p I J → K (p , ( I , J))))
```

### A decreasing sequence of natural numbers cannot have arbitrarily large strict decreasing values

```agda
module _
  {f : sequence ℕ} (H : is-decreasing-sequence-ℕ f)
  (K : (N : ℕ) → Σ ℕ (is-∞-strict-decreasing-value-sequence-ℕ f N))
  where

  extract-∞-strict-decreasing-value-sequence-ℕ : ℕ → ℕ
  extract-∞-strict-decreasing-value-sequence-ℕ zero-ℕ = pr1 (K zero-ℕ)
  extract-∞-strict-decreasing-value-sequence-ℕ (succ-ℕ n) =
    pr1 (K (succ-ℕ (extract-∞-strict-decreasing-value-sequence-ℕ n)))

  is-strict-value-∞-strict-decreasing-value-sequence-ℕ :
    (n : ℕ) →
    is-strict-decreasing-value-sequence-ℕ f
      (extract-∞-strict-decreasing-value-sequence-ℕ n)
  is-strict-value-∞-strict-decreasing-value-sequence-ℕ zero-ℕ =
    pr2 (pr2 (K zero-ℕ))
  is-strict-value-∞-strict-decreasing-value-sequence-ℕ (succ-ℕ n) =
    pr2 (pr2 (K (succ-ℕ (extract-∞-strict-decreasing-value-sequence-ℕ n))))

  leq-succ-extract-∞-strict-decreasing-value-sequence-ℕ :
    (n : ℕ) →
    leq-ℕ
      (succ-ℕ (extract-∞-strict-decreasing-value-sequence-ℕ n))
      (extract-∞-strict-decreasing-value-sequence-ℕ (succ-ℕ n))
  leq-succ-extract-∞-strict-decreasing-value-sequence-ℕ n =
    pr1
      ( pr2
        ( K
          ( succ-ℕ
            ( extract-∞-strict-decreasing-value-sequence-ℕ n))))

  no-∞-strict-decreasing-value-decreasing-sequence-ℕ : empty
  no-∞-strict-decreasing-value-decreasing-sequence-ℕ =
    no-strict-decreasing-value-sequence-ℕ
      ( f ∘ extract-∞-strict-decreasing-value-sequence-ℕ)
      ( λ n →
        concatenate-leq-le-ℕ
        { f (extract-∞-strict-decreasing-value-sequence-ℕ (succ-ℕ n))}
        { f (succ-ℕ (extract-∞-strict-decreasing-value-sequence-ℕ n))}
        { f (extract-∞-strict-decreasing-value-sequence-ℕ n)}
        ( H
          ( succ-ℕ (extract-∞-strict-decreasing-value-sequence-ℕ n))
          ( extract-∞-strict-decreasing-value-sequence-ℕ (succ-ℕ n))
        ( leq-succ-extract-∞-strict-decreasing-value-sequence-ℕ n))
        ( is-strict-value-∞-strict-decreasing-value-sequence-ℕ n))
```

### The subsequences of a decreasing sequence of natural numbers don't all have a strict decreasing value

```agda
module _
  {u : sequence ℕ} (H : is-decreasing-sequence-ℕ u)
  (K : Π-subsequence (Σ ℕ ∘ is-strict-decreasing-value-sequence-ℕ) u)
  where

  extract-strict-decreasing-value-subsequence-ℕ : ℕ → ℕ
  extract-strict-decreasing-value-subsequence-ℕ zero-ℕ =
    pr1 (K (refl-subsequence u))
  extract-strict-decreasing-value-subsequence-ℕ (succ-ℕ n) =
    skip-ℕ
      ( extract-strict-decreasing-value-subsequence-ℕ n)
      ( pr1
        ( K
          ( skip-subsequence
            ( extract-strict-decreasing-value-subsequence-ℕ n)
            ( u))))

  is-strict-value-extract-strict-decreasing-value-subsequence-ℕ :
    (n : ℕ) →
    is-strict-decreasing-value-sequence-ℕ u
      (extract-strict-decreasing-value-subsequence-ℕ n)
  is-strict-value-extract-strict-decreasing-value-subsequence-ℕ zero-ℕ =
    pr2 (K (refl-subsequence u))
  is-strict-value-extract-strict-decreasing-value-subsequence-ℕ (succ-ℕ n) =
    pr2
      ( K
        ( skip-subsequence
          ( extract-strict-decreasing-value-subsequence-ℕ n)
          ( u)))

  no-strict-decreasing-value-Π-subsequence-ℕ : empty
  no-strict-decreasing-value-Π-subsequence-ℕ =
    no-strict-decreasing-value-sequence-ℕ
      ( u ∘ extract-strict-decreasing-value-subsequence-ℕ)
      ( λ n →
        concatenate-leq-le-ℕ
        { u (extract-strict-decreasing-value-subsequence-ℕ (succ-ℕ n))}
        { u (succ-ℕ (extract-strict-decreasing-value-subsequence-ℕ n))}
        { u (extract-strict-decreasing-value-subsequence-ℕ n)}
        ( H
          ( succ-ℕ (extract-strict-decreasing-value-subsequence-ℕ n))
          ( skip-ℕ
            ( extract-strict-decreasing-value-subsequence-ℕ n)
            ( pr1
              ( K
              ( strict-increasing-skip-ℕ
                ( extract-strict-decreasing-value-subsequence-ℕ n)))))
          ( leq-add-ℕ
            ( extract-strict-decreasing-value-subsequence-ℕ n)
            ( pr1
              ( K
              ( strict-increasing-skip-ℕ
                ( extract-strict-decreasing-value-subsequence-ℕ n))))))
        ( is-strict-value-extract-strict-decreasing-value-subsequence-ℕ n))
```

### Decreasing sequences of natural numbers have arbitrarily long stationnary intervals

```agda
stationnary-interval-bounded-decreasing-sequence-ℕ :
    (u : sequence ℕ) (H : is-decreasing-sequence-ℕ u) (M : ℕ) →
    (leq-ℕ (u zero-ℕ) M) →
    ((p : ℕ) → Σ ℕ (λ n → u (p +ℕ n) ＝ u n))
stationnary-interval-bounded-decreasing-sequence-ℕ u H zero-ℕ I p =
  ( zero-ℕ ,
    antisymmetric-leq-ℕ
      ( u p)
      ( u zero-ℕ)
      ( H zero-ℕ p (leq-zero-ℕ p))
      ( transitive-leq-ℕ (u 0) 0 (u p) (leq-zero-ℕ (u p)) I))
stationnary-interval-bounded-decreasing-sequence-ℕ u H (succ-ℕ M) I p =
  rec-coproduct
    ( λ J → (zero-ℕ , J))
    ( λ J →
      rec-Σ
        ( λ k H → (skip-ℕ p k , H))
        ( stationnary-interval-bounded-decreasing-sequence-ℕ
          ( sequence-subsequence u (skip-subsequence p u))
          ( decreasing-Π-subsequence-decreasing-sequence-poset
            ( ℕ-Poset)
            ( u)
            ( H)
            ( skip-subsequence p u))
          ( M)
          ( transitive-leq-ℕ
            ( u (succ-ℕ p))
            ( u p)
            ( M)
            ( leq-le-succ-ℕ
              ( u p)
              ( M)
              ( concatenate-le-leq-ℕ {u p} {u 0} {succ-ℕ M} J I))
              ( H p (succ-ℕ p) (succ-leq-ℕ p)))
          ( p)))
    ( eq-or-le-leq-ℕ
      ( u p)
      ( u zero-ℕ)
      ( H zero-ℕ p (leq-zero-ℕ p)))

module _
  {u : sequence ℕ} (H : is-decreasing-sequence-ℕ u)
  where

  stationnary-interval-decreasing-sequence-ℕ :
    (p : ℕ) → Σ ℕ (λ n → u (p +ℕ n) ＝ u n)
  stationnary-interval-decreasing-sequence-ℕ =
    stationnary-interval-bounded-decreasing-sequence-ℕ
      ( u)
      ( H)
      ( u 0)
      ( refl-leq-ℕ (u 0))
```

## External links

- [Decreasing sequences of natural numbers](https://ncatlab.org/nlab/show/natural+number#decreasing_sequences_of_natural_numbers)
  at $n$Lab
