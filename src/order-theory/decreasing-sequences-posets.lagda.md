# Decreasing sequences in partially ordered sets

```agda
module order-theory.decreasing-sequences-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strictly-increasing-sequences-natural-numbers

open import foundation.asymptotical-dependent-sequences
open import foundation.asymptotically-constant-sequences
open import foundation.constant-sequences
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.subsequences
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.sequences-posets
```

</details>

## Idea

A [sequence in a partially ordered set](order-theory.sequences-posets.md) is
**decreasing** if it reverses the
[standard ordering on the natural numbers](elementary-number-theory.inequality-natural-numbers.md).

## Definitions

### Decreasing sequences in partially ordered sets

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u : sequence-poset P)
  where

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

### A sequence in a partially ordered set is decreasing if and only if all its values are decreasing

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {u : sequence-poset P}
  where

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

### Any subsequence of a decreasing sequence in a partially ordered set is decreasing

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u : sequence-poset P)
  where

  decreasing-Π-subsequence-decreasing-sequence-poset :
    is-decreasing-sequence-poset P u →
    Π-subsequence (is-decreasing-sequence-poset P) u
  decreasing-Π-subsequence-decreasing-sequence-poset H v p q I =
    H
      ( extract-subsequence u v p)
      ( extract-subsequence u v q)
      ( preserves-leq-extract-subsequence u v p q I)
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

  Π-subsequence-leq-decreasing-sequence-poset :
    is-decreasing-sequence-poset P u →
    Π-subsequence (λ v → leq-sequence-poset P v u) u
  Π-subsequence-leq-decreasing-sequence-poset H v n =
    H n (extract-subsequence u v n) (leq-id-extract-subsequence u v n)
```

### A decreasing sequence `u` with `u (p + n) ＝ u n` is constant between `n` and `p + n`

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u : sequence-poset P)
  (p n : ℕ) (I : u (p +ℕ n) ＝ u n)
  where

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

### A decreasing sequence in a partially ordered set with a constant subsequence is asymptotically constant

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {u : sequence-poset P}
  where

  ∞-constant-Σ-subsequence-constant-decreasing-sequence-poset :
    is-decreasing-sequence-poset P u →
    Σ-subsequence is-constant-sequence u →
    is-∞-constant-sequence u
  ∞-constant-Σ-subsequence-constant-decreasing-sequence-poset H =
    rec-Σ
      ( λ v K →
        ∞-constant-is-∞-value-sequence
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

### A decreasing sequence in a partially ordered set with an asymptotically constant subsequence is asymptotically constant

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {u : sequence-poset P}
  where

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
