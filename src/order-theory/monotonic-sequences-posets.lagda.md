# Monotonic sequences in partially ordered sets

```agda
module order-theory.monotonic-sequences-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-monotonic-sequences-natural-numbers

open import foundation.asymptotical-dependent-sequences
open import foundation.asymptotically-constant-sequences
open import foundation.binary-relations
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
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.sequences-posets
```

</details>

## Idea

Monotonic sequences in partially ordered sets are sequences that preserve or
reverse the
[standard ordering on the natural numbers](elementary-number-theory.inequality-natural-numbers.md).

## Definitions

### Monotonic values of sequences in partially ordered sets

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u : sequence-poset P) (n : ℕ)
  where

  is-increasing-value-prop-sequence-poset : Prop l2
  is-increasing-value-prop-sequence-poset =
    leq-Poset-Prop P (u n) (u (succ-ℕ n))

  is-increasing-value-sequence-poset : UU l2
  is-increasing-value-sequence-poset =
    type-Prop is-increasing-value-prop-sequence-poset

  is-prop-is-increasing-value-sequence-poset :
    is-prop is-increasing-value-sequence-poset
  is-prop-is-increasing-value-sequence-poset =
    is-prop-type-Prop is-increasing-value-prop-sequence-poset

  is-decreasing-value-prop-sequence-poset : Prop l2
  is-decreasing-value-prop-sequence-poset =
    leq-Poset-Prop P (u (succ-ℕ n)) (u n)

  is-decreasing-value-sequence-poset : UU l2
  is-decreasing-value-sequence-poset =
    type-Prop is-decreasing-value-prop-sequence-poset

  is-prop-is-decreasing-value-sequence-poset :
    is-prop is-decreasing-value-sequence-poset
  is-prop-is-decreasing-value-sequence-poset =
    is-prop-type-Prop is-decreasing-value-prop-sequence-poset
```

### Monotonic sequences in partially ordered sets

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u : sequence-poset P)
  where

  is-increasing-prop-sequence-poset : Prop l2
  is-increasing-prop-sequence-poset =
      Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j →
            hom-Prop
              ( leq-ℕ-Prop i j)
              ( leq-Poset-Prop P (u i) (u j))))

  is-increasing-sequence-poset : UU l2
  is-increasing-sequence-poset =
    type-Prop is-increasing-prop-sequence-poset

  is-prop-is-increasing-sequence-poset :
    is-prop is-increasing-sequence-poset
  is-prop-is-increasing-sequence-poset =
    is-prop-type-Prop is-increasing-prop-sequence-poset

  is-decreasing-prop-sequence-poset : Prop l2
  is-decreasing-prop-sequence-poset =
      Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j →
            hom-Prop
              ( leq-ℕ-Prop i j)
              ( leq-Poset-Prop P (u j) (u i))))

  is-decreasing-sequence-poset : UU l2
  is-decreasing-sequence-poset =
    type-Prop is-decreasing-prop-sequence-poset

  is-prop-is-decreasing-sequence-poset :
    is-prop is-decreasing-sequence-poset
  is-prop-is-decreasing-sequence-poset =
    is-prop-type-Prop is-decreasing-prop-sequence-poset
```

## Properties

### Any value of a sequence in a partially ordered set is stationnary if and only if it is both increasing and decreasing

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u : sequence-poset P) (n : ℕ)
  where

  increasing-value-is-stationnary-value-sequence-poset :
    is-stationnary-value-sequence u n →
    is-increasing-value-sequence-poset P u n
  increasing-value-is-stationnary-value-sequence-poset H =
    leq-eq-Poset P H

  decreasing-value-is-stationnary-value-sequence-poset :
    is-stationnary-value-sequence u n →
    is-decreasing-value-sequence-poset P u n
  decreasing-value-is-stationnary-value-sequence-poset H =
    leq-eq-Poset P (inv H)

  stationnary-value-is-increasing-decreasing-value-sequence-poset :
    is-increasing-value-sequence-poset P u n →
    is-decreasing-value-sequence-poset P u n →
    is-stationnary-value-sequence u n
  stationnary-value-is-increasing-decreasing-value-sequence-poset =
    antisymmetric-leq-Poset P (u n) (u (succ-ℕ n))
```

### A sequence in a partially ordered set is monotonic if and only if all its values are monotonic with the same monotonicity

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {u : sequence-poset P}
  where

  increasing-sequence-is-increasing-value-sequence-poset :
    ((n : ℕ) → is-increasing-value-sequence-poset P u n) →
    is-increasing-sequence-poset P u
  increasing-sequence-is-increasing-value-sequence-poset H p =
    based-ind-ℕ
      ( p)
      ( λ q → leq-Poset P (u p) (u q))
      ( refl-leq-Poset P (u p))
      ( λ q I →
        transitive-leq-Poset P (u p) (u q) (u (succ-ℕ q)) (H q))

  increasing-value-is-increasing-sequence-poset :
    is-increasing-sequence-poset P u →
    ((n : ℕ) → is-increasing-value-sequence-poset P u n)
  increasing-value-is-increasing-sequence-poset H n =
    H n (succ-ℕ n) (succ-leq-ℕ n)

  decreasing-sequence-is-decreasing-value-sequence-poset :
    ((n : ℕ) → is-decreasing-value-sequence-poset P u n) →
    is-decreasing-sequence-poset P u
  decreasing-sequence-is-decreasing-value-sequence-poset H p =
    based-ind-ℕ
      ( p)
      ( λ q → leq-Poset P (u q) (u p))
      ( refl-leq-Poset P (u p))
      ( λ q I J →
        transitive-leq-Poset P (u (succ-ℕ q)) (u q) (u p) J (H q))

  decreasing-value-is-decreasing-sequence-poset :
    is-decreasing-sequence-poset P u →
    ((n : ℕ) → is-decreasing-value-sequence-poset P u n)
  decreasing-value-is-decreasing-sequence-poset H n =
    H n (succ-ℕ n) (succ-leq-ℕ n)
```

### A sequence in a partially ordered set is constant if and only if it is both increasing and decreasing

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {u : sequence-poset P}
  where

  increasing-is-constant-sequence-poset :
    is-constant-sequence u → is-increasing-sequence-poset P u
  increasing-is-constant-sequence-poset H p q I = leq-eq-Poset P (H p q)

  decreasing-is-constant-sequence-poset :
    is-constant-sequence u → is-decreasing-sequence-poset P u
  decreasing-is-constant-sequence-poset H p q I = leq-eq-Poset P (H q p)

  constant-is-increasing-decreasing-sequence-poset :
    is-increasing-sequence-poset P u →
    is-decreasing-sequence-poset P u →
    is-constant-sequence u
  constant-is-increasing-decreasing-sequence-poset I J p q =
    rec-coproduct
      ( λ H → antisymmetric-leq-Poset P (u p) (u q) (I p q H) (J p q H))
      ( λ H → antisymmetric-leq-Poset P (u p) (u q) (J q p H) (I q p H))
      ( linear-leq-ℕ p q)
```

### Any subsequence of a monotonic sequence in a partially ordered set is monotonic

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u : sequence-poset P)
  where

  increasing-Π-subsequence-increasing-sequence-poset :
    is-increasing-sequence-poset P u →
    Π-subsequence (is-increasing-sequence-poset P) u
  increasing-Π-subsequence-increasing-sequence-poset H v p q I =
    H
      ( extract-subsequence u v p)
      ( extract-subsequence u v q)
      ( preserves-leq-extract-subsequence u v p q I)

  decreasing-Π-subsequence-decreasing-sequence-poset :
    is-decreasing-sequence-poset P u →
    Π-subsequence (is-decreasing-sequence-poset P) u
  decreasing-Π-subsequence-decreasing-sequence-poset H v p q I =
    H
      ( extract-subsequence u v p)
      ( extract-subsequence u v q)
      ( preserves-leq-extract-subsequence u v p q I)
```

### A sequence in a partially ordered set is increasing if and only if it is lesser than all its subsequences

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u : sequence-poset P)
  where

  increasing-Π-subsequence-leq-sequence-poset :
    Π-subsequence (λ v → leq-sequence-poset P u v) u →
    is-increasing-sequence-poset P u
  increasing-Π-subsequence-leq-sequence-poset H =
    increasing-sequence-is-increasing-value-sequence-poset
      ( P)
      ( H (skip-zero-sequence u))

  Π-subsequence-leq-increasing-sequence-Poset :
    is-increasing-sequence-poset P u →
    Π-subsequence (λ v → leq-sequence-poset P u v) u
  Π-subsequence-leq-increasing-sequence-Poset H v n =
    H n (extract-subsequence u v n) (leq-id-extract-subsequence u v n)
```

### A sequence in a partially ordered set is decreasing if and only if it is greater than all its subsequences

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u : sequence-poset P)
  where

  decreasing-Π-subsequence-leq-sequence-poset :
    Π-subsequence (λ v → leq-sequence-poset P v u) u →
    is-decreasing-sequence-poset P u
  decreasing-Π-subsequence-leq-sequence-poset H =
    decreasing-sequence-is-decreasing-value-sequence-poset
      ( P)
      ( H (skip-zero-sequence u))

  Π-subsequence-leq-decreasing-sequence-Poset :
    is-decreasing-sequence-poset P u →
    Π-subsequence (λ v → leq-sequence-poset P v u) u
  Π-subsequence-leq-decreasing-sequence-Poset H v n =
    H n (extract-subsequence u v n) (leq-id-extract-subsequence u v n)
```

### A monotonic sequence `u` with `u (p + n) ＝ u p` is constant between `n` and `p + n`

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u : sequence-poset P)
  (p n : ℕ) (I : u (p +ℕ n) ＝ u n)
  where

  constant-value-is-stationnary-interval-increasing-sequence-poset :
    is-increasing-sequence-poset P u →
    (k : ℕ) (J : leq-ℕ k p) → u (k +ℕ n) ＝ u n
  constant-value-is-stationnary-interval-increasing-sequence-poset H k J =
    antisymmetric-leq-Poset
      ( P)
      ( u (k +ℕ n))
      ( u n)
      ( concatenate-leq-eq-Poset
        ( P)
        ( H (k +ℕ n) (p +ℕ n) (preserves-leq-left-add-ℕ n k p J))
        ( I))
      ( H n (k +ℕ n) (leq-add-ℕ' n k))

  constant-value-is-stationnary-interval-decreasing-sequence-poset :
    is-decreasing-sequence-poset P u →
    (k : ℕ) (J : leq-ℕ k p) → u (k +ℕ n) ＝ u n
  constant-value-is-stationnary-interval-decreasing-sequence-poset H k J =
    antisymmetric-leq-Poset
      ( P)
      ( u (k +ℕ n))
      ( u n)
      ( H n (k +ℕ n) (leq-add-ℕ' n k))
      ( concatenate-eq-leq-Poset
        ( P)
        ( inv I)
        ( H (k +ℕ n) (p +ℕ n) (preserves-leq-left-add-ℕ n k p J)))
```

### Asymptotical behavior

#### A monotonic sequence in a partially ordered set with a constant subsequence is asymptotically constant

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {u : sequence-poset P}
  where

  ∞-constant-Σ-subsequence-constant-increasing-sequence-poset :
    is-increasing-sequence-poset P u →
    Σ-subsequence is-constant-sequence u →
    is-∞-constant-sequence u
  ∞-constant-Σ-subsequence-constant-increasing-sequence-poset H =
    rec-Σ
      ( λ v K →
        ∞-constant-eq-∞-constant-sequence
          ( u (extract-subsequence u v zero-ℕ))
          ( u)
          ( ( extract-subsequence u v zero-ℕ) ,
            ( λ n I →
              antisymmetric-leq-Poset
                ( P)
                ( sequence-subsequence u v zero-ℕ)
                ( u n)
                ( H (extract-subsequence u v zero-ℕ) n I)
                ( concatenate-leq-eq-Poset
                  ( P)
                  ( H
                    ( n)
                    ( extract-modulus-subsequence u v n)
                    ( leq-extract-modulus-subsequence u v n))
                  ( K (modulus-subsequence u v n) zero-ℕ)))))

  ∞-constant-Σ-subsequence-constant-decreasing-sequence-poset :
    is-decreasing-sequence-poset P u →
    Σ-subsequence is-constant-sequence u →
    is-∞-constant-sequence u
  ∞-constant-Σ-subsequence-constant-decreasing-sequence-poset H =
    rec-Σ
      ( λ v K →
        ∞-constant-eq-∞-constant-sequence
          ( u (extract-subsequence u v zero-ℕ))
          ( u)
          ( ( extract-subsequence u v zero-ℕ) ,
            ( λ n I →
              antisymmetric-leq-Poset
                ( P)
                ( sequence-subsequence u v zero-ℕ)
                ( u n)
                ( concatenate-eq-leq-Poset
                  ( P)
                  ( K zero-ℕ (modulus-subsequence u v n))
                  ( H
                    ( n)
                    ( extract-modulus-subsequence u v n)
                    ( leq-extract-modulus-subsequence u v n)))
                ( H (extract-subsequence u v zero-ℕ) n I))))
```

#### A monotonic sequence in a partially ordered set with an asymptotically constant subsequence is asymptotically constant

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {u : sequence-poset P}
  where

  ∞-constant-Σ-subsequence-∞-constant-increasing-sequence-poset :
    is-increasing-sequence-poset P u →
    Σ-subsequence is-∞-constant-sequence u →
    is-∞-constant-sequence u
  ∞-constant-Σ-subsequence-∞-constant-increasing-sequence-poset H =
    ( ∞-constant-Σ-subsequence-constant-increasing-sequence-poset P H) ∘
    ( rec-Σ
      ( λ v →
        ( rec-Σ ( λ w I → ( sub-subsequence u v w , I))) ∘
        ( constant-subsequence-is-∞-constant-sequence
          ( sequence-subsequence u v))))

  ∞-constant-Σ-subsequence-∞-constant-decreasing-sequence-poset :
    is-decreasing-sequence-poset P u →
    Σ-subsequence is-∞-constant-sequence u →
    is-∞-constant-sequence u
  ∞-constant-Σ-subsequence-∞-constant-decreasing-sequence-poset H =
    ( ∞-constant-Σ-subsequence-constant-decreasing-sequence-poset P H) ∘
    ( rec-Σ
      ( λ v →
        ( rec-Σ (λ w I → (sub-subsequence u v w , I))) ∘
        ( constant-subsequence-is-∞-constant-sequence
          ( sequence-subsequence u v))))
```

#### An increasing sequence in a partially ordered set with a decreasing subsequence is asymptotically constant

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {u : sequence-poset P}
  (H : is-increasing-sequence-poset P u)
  where

  ∞-constant-Σ-subsequence-decreasing-is-increasing-sequence-poset :
    Σ-subsequence (is-decreasing-sequence-poset P) u →
    is-∞-constant-sequence u
  ∞-constant-Σ-subsequence-decreasing-is-increasing-sequence-poset =
    ( ∞-constant-Σ-subsequence-constant-increasing-sequence-poset P H) ∘
    ( tot
      ( (constant-is-increasing-decreasing-sequence-poset P) ∘
        ( increasing-Π-subsequence-increasing-sequence-poset P u H)))
```

#### A decreasing sequence in a partially ordered set with an increasing subsequence is asymptotically constant

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {u : sequence-poset P}
  (H : is-decreasing-sequence-poset P u)
  where

  ∞-constant-Σ-subsequence-increasing-is-decreasing-sequence-poset :
    Σ-subsequence (is-increasing-sequence-poset P) u →
    is-∞-constant-sequence u
  ∞-constant-Σ-subsequence-increasing-is-decreasing-sequence-poset =
    ( ∞-constant-Σ-subsequence-constant-decreasing-sequence-poset P H) ∘
    ( tot
      ( λ v K →
        constant-is-increasing-decreasing-sequence-poset
          ( P)
          ( K)
          ( decreasing-Π-subsequence-decreasing-sequence-poset P u H v)))
```
