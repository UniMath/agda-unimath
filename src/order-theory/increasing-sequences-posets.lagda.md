# Increasing sequences in partially ordered sets

```agda
module order-theory.increasing-sequences-posets where
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
**increasing** if it preserves the
[standard ordering on the natural numbers](elementary-number-theory.inequality-natural-numbers.md).

## Definitions

### Increasing sequences in partially ordered sets

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
```

## Properties

### A sequence in a partially ordered set is increasing if and only if all its values are increasing

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
```

### Any subsequence of an increasing sequence in a partially ordered set is increasing

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

### An increasing sequence `u` with `u (p + n) ＝ u n` is constant between `n` and `p + n`

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
```

### An increasing sequence in a partially ordered set with a constant subsequence is asymptotically constant

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
        ∞-constant-is-∞-value-sequence
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
```

### An increasing sequence in a partially ordered set with an asymptotically constant subsequence is asymptotically constant

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
```
