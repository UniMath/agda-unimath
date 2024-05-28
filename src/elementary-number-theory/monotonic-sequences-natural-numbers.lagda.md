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
```

</details>

## Idea

Monotonic sequences of natural numbers are functions `f : ℕ → ℕ` that preserve
or reverse inequality of natural numbers.

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

## Strictly increasing sequences of natural numbers are monotonic

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

  is-increasing-is-strict-increasing-sequence-ℕ :
    is-strict-increasing-sequence-ℕ f → is-increasing-sequence-ℕ f
  is-increasing-is-strict-increasing-sequence-ℕ H =
    is-increasing-is-increasing-value-sequence-ℕ f
      ( λ n → is-increasing-value-is-strict-increasing-value-sequence-ℕ n
        ( is-strict-increasing-value-is-strict-increasing-sequence-ℕ f H n))
```

### A sequence of natural numbers is constant if and only if it is increasing and decreasing

```agda
module _
  (f : sequence ℕ)
  where

  is-increasing-is-constant-sequence-ℕ :
    is-constant-sequence f → is-increasing-sequence-ℕ f
  is-increasing-is-constant-sequence-ℕ H p q I = leq-eq-ℕ (f p) (f q) (H p q)

  is-decreasing-is-constant-sequence-ℕ :
    is-constant-sequence f → is-decreasing-sequence-ℕ f
  is-decreasing-is-constant-sequence-ℕ H p q I = leq-eq-ℕ (f q) (f p) (H q p)

  is-constant-is-increasing-decreasing-sequence-ℕ :
    is-increasing-sequence-ℕ f →
    is-decreasing-sequence-ℕ f →
    is-constant-sequence f
  is-constant-is-increasing-decreasing-sequence-ℕ I J p q =
    rec-coproduct
      ( λ H → antisymmetric-leq-ℕ (f p) (f q) (I p q H) (J p q H))
      ( λ H → antisymmetric-leq-ℕ (f p) (f q) (J q p H) (I q p H))
      ( linear-leq-ℕ p q)
```

### Any subsequence of a monotonic sequence of natural numbers is monotonic

```agda
module _
  (u : sequence ℕ)
  where

  is-increasing-Π-subsequence-ℕ :
    (H : is-increasing-sequence-ℕ u) → Π-subsequence is-increasing-sequence-ℕ u
  is-increasing-Π-subsequence-ℕ H v p q I =
    H
      ( extract-subsequence u v p)
      ( extract-subsequence u v q)
      ( is-increasing-is-strict-increasing-sequence-ℕ
        ( extract-subsequence u v)
        ( is-strict-increasing-extract-subsequence u v)
        ( p)
        ( q)
        ( I))

  is-decreasing-Π-subsequence-ℕ :
    (H : is-decreasing-sequence-ℕ u) → Π-subsequence is-decreasing-sequence-ℕ u
  is-decreasing-Π-subsequence-ℕ H v p q I =
    H
      ( extract-subsequence u v p)
      ( extract-subsequence u v q)
      ( is-increasing-is-strict-increasing-sequence-ℕ
        ( extract-subsequence u v)
        ( is-strict-increasing-extract-subsequence u v)
        ( p)
        ( q)
        ( I))
```

### A monotonic sequence of natural numbers with a constant subsequence is asymptotically constant

```agda
module _
  {u : sequence ℕ}
  where

  is-∞-constant-is-constant-subsequence-increasing-sequence-ℕ :
    is-increasing-sequence-ℕ u →
    Σ-subsequence is-constant-sequence u →
    is-∞-constant-sequence u
  is-∞-constant-is-constant-subsequence-increasing-sequence-ℕ H =
    rec-Σ
      ( λ v K →
      is-∞-constant-eq-∞-constant-sequence
        ( u (extract-subsequence u v zero-ℕ))
        ( u)
        ( ( extract-subsequence u v zero-ℕ) ,
          ( λ n I →
            antisymmetric-leq-ℕ
              ( u (extract-subsequence u v zero-ℕ))
              ( u n)
              ( H (extract-subsequence u v zero-ℕ) n I)
              ( tr
                ( leq-ℕ (u n))
                ( K (modulus-subsequence u v n) zero-ℕ)
                ( H
                  ( n)
                  ( extract-modulus-subsequence u v n)
                  ( leq-extract-modulus-subsequence u v n))))))

  is-∞-constant-is-constant-subsequence-decreasing-sequence-ℕ :
    is-decreasing-sequence-ℕ u →
    Σ-subsequence is-constant-sequence u →
    is-∞-constant-sequence u
  is-∞-constant-is-constant-subsequence-decreasing-sequence-ℕ H =
    rec-Σ
      ( λ v K →
      is-∞-constant-eq-∞-constant-sequence
        ( u (extract-subsequence u v zero-ℕ))
        ( u)
        ( ( extract-subsequence u v zero-ℕ) ,
          ( λ n I →
            antisymmetric-leq-ℕ
              ( u (extract-subsequence u v zero-ℕ))
              ( u n)
              ( tr
                ( λ k → leq-ℕ k (u n))
                ( K (modulus-subsequence u v n) zero-ℕ)
                ( H
                  ( n)
                  ( extract-modulus-subsequence u v n)
                  ( leq-extract-modulus-subsequence u v n)))
              ( H (extract-subsequence u v zero-ℕ) n I))))
```

### A monotonic sequence of natural numbers with an asymptotically constant subsequence is asymptotically constant

```agda
module _
  {u : sequence ℕ}
  where

  is-∞-constant-is-∞-constant-subsequence-increasing-sequence-ℕ :
    is-increasing-sequence-ℕ u →
    Σ-subsequence is-∞-constant-sequence u →
    is-∞-constant-sequence u
  is-∞-constant-is-∞-constant-subsequence-increasing-sequence-ℕ H =
    ( is-∞-constant-is-constant-subsequence-increasing-sequence-ℕ H) ∘
    ( rec-Σ
      ( λ v →
        ( rec-Σ ( λ w I → ( sub-subsequence u v w , I))) ∘
        ( constant-subsequence-is-∞-constant-sequence
          ( sequence-subsequence u v))))

  is-∞-constant-is-∞-constant-subsequence-decreasing-sequence-ℕ :
    is-decreasing-sequence-ℕ u →
    Σ-subsequence is-∞-constant-sequence u →
    is-∞-constant-sequence u
  is-∞-constant-is-∞-constant-subsequence-decreasing-sequence-ℕ H =
    ( is-∞-constant-is-constant-subsequence-decreasing-sequence-ℕ H) ∘
    ( rec-Σ
      ( λ v →
        ( rec-Σ (λ w I → (sub-subsequence u v w , I))) ∘
        ( constant-subsequence-is-∞-constant-sequence
          ( sequence-subsequence u v))))
```

### A decreasing sequence of natural numbers with an increasing subsequence is asymptotically constant

```agda
module _
  {u : sequence ℕ} (H : is-decreasing-sequence-ℕ u)
  where

  is-∞-constant-is-increasing-subsequence-decreasing-subsequence-ℕ :
    Σ-subsequence is-increasing-sequence-ℕ u → is-∞-constant-sequence u
  is-∞-constant-is-increasing-subsequence-decreasing-subsequence-ℕ =
    ( is-∞-constant-is-constant-subsequence-decreasing-sequence-ℕ H) ∘
    ( tot
      ( λ v K →
        is-constant-is-increasing-decreasing-sequence-ℕ
          ( sequence-subsequence u v)
          ( K)
          ( is-decreasing-Π-subsequence-ℕ u H v)))
```

### An increasing sequence of natural numbers with an decreasing subsequence is asymptotically constant

```agda
module _
  {u : sequence ℕ} (H : is-increasing-sequence-ℕ u)
  where

  is-∞-constant-is-decreasing-subsequence-increasing-subsequence-ℕ :
    Σ-subsequence is-decreasing-sequence-ℕ u → is-∞-constant-sequence u
  is-∞-constant-is-decreasing-subsequence-increasing-subsequence-ℕ =
    ( is-∞-constant-is-constant-subsequence-increasing-sequence-ℕ H) ∘
    ( tot
      ( λ v K →
        is-constant-is-increasing-decreasing-sequence-ℕ
          ( sequence-subsequence u v)
          ( is-increasing-Π-subsequence-ℕ u H v)
          ( K)))
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

### Any value of a monotonic sequence of natural numbers that is not a strict value is stationnary

```agda
module _
  (f : sequence ℕ)
  where

  is-stationnary-is-not-strict-value-increasing-sequence-ℕ :
    is-increasing-sequence-ℕ f →
    (n : ℕ) →
    ¬ (is-strict-increasing-value-sequence-ℕ f n) →
    is-stationnary-value-sequence f n
  is-stationnary-is-not-strict-value-increasing-sequence-ℕ H n K =
    map-right-unit-law-coproduct-is-empty
      ( is-stationnary-value-sequence f n)
      ( is-strict-increasing-value-sequence-ℕ f n)
      ( K)
      ( decide-is-stationnary-is-increasing-value-sequence-ℕ
        ( f)
        ( n)
        ( is-increasing-value-is-increasing-sequence-ℕ f H n))

  is-stationnary-is-not-strict-value-decreasing-sequence-ℕ :
    is-decreasing-sequence-ℕ f →
    (n : ℕ) →
    ¬ (is-strict-decreasing-value-sequence-ℕ f n) →
    is-stationnary-value-sequence f n
  is-stationnary-is-not-strict-value-decreasing-sequence-ℕ H n K =
    map-right-unit-law-coproduct-is-empty
      ( is-stationnary-value-sequence f n)
      ( is-strict-decreasing-value-sequence-ℕ f n)
      ( K)
      ( decide-is-stationnary-is-decreasing-value-sequence-ℕ
        ( f)
        ( n)
        ( is-decreasing-value-is-decreasing-sequence-ℕ f H n))
```

### A decreasing sequence of natural numbers that takes the value zero is asymptotically equal to zero

```agda
module _
  {f : sequence ℕ} (H : is-decreasing-sequence-ℕ f)
  where

  is-∞-zero-is-zero-value-decreasing-sequence-ℕ :
    Σ ℕ (λ n → zero-ℕ ＝ f n) → asymptotically (λ n → zero-ℕ ＝ f n)
  is-∞-zero-is-zero-value-decreasing-sequence-ℕ =
    tot
      ( λ n K k I →
        is-zero-leq-zero-ℕ'
          ( f k)
          ( inv-tr (leq-ℕ (f k)) K (H n k I)))
```

### A decreasing sequence of natural numbers that has no strictly decreasing value is constant

```agda
module _
  {f : sequence ℕ} (H : is-decreasing-sequence-ℕ f)
  where

  is-constant-no-strict-decreasing-value-decreasing-sequence-ℕ :
    ((n : ℕ) → ¬ (is-strict-decreasing-value-sequence-ℕ f n)) →
    is-constant-sequence f
  is-constant-no-strict-decreasing-value-decreasing-sequence-ℕ K =
    is-constant-is-stationnary-value-sequence f
      ( λ n →
        is-stationnary-is-not-strict-value-decreasing-sequence-ℕ
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

  is-∞-constant-∞-no-strict-value-decreasing-sequence-ℕ :
    asymptotically (λ n → ¬ (is-strict-decreasing-value-sequence-ℕ f n)) →
    is-∞-constant-sequence f
  is-∞-constant-∞-no-strict-value-decreasing-sequence-ℕ =
    ( is-∞-constant-is-∞-stationnary-sequence f) ∘
    ( map-asymptotically-Π
      ( is-stationnary-is-not-strict-value-decreasing-sequence-ℕ f H))
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

  is-∞-constant-is-upper-bounded-strict-value-decreasing-sequence-ℕ :
    Σ ℕ (is-upper-bound-strict-decreasing-value-sequence-ℕ f) →
    is-∞-constant-sequence f
  is-∞-constant-is-upper-bounded-strict-value-decreasing-sequence-ℕ =
    ( is-∞-constant-∞-no-strict-value-decreasing-sequence-ℕ H) ∘
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

  is-∞-constant-no-∞-strict-decreasing-value-decreasing-sequence-ℕ :
    Σ ℕ (λ N → ¬ Σ ℕ (is-∞-strict-decreasing-value-sequence-ℕ f N)) →
    is-∞-constant-sequence f
  is-∞-constant-no-∞-strict-decreasing-value-decreasing-sequence-ℕ =
    ( is-∞-constant-∞-no-strict-value-decreasing-sequence-ℕ H) ∘
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
