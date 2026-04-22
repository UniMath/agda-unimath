# Partitions of closed intervals of real numbers

```agda
module real-numbers.partitions-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.tuples

open import order-theory.increasing-arrays-posets
open import order-theory.increasing-finite-sequences-posets
open import order-theory.increasing-nonempty-arrays-posets
open import order-theory.large-posets
open import order-theory.least-upper-bounds-large-posets
open import order-theory.opposite-posets
open import order-theory.order-preserving-maps-posets

open import real-numbers.addition-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maximum-finite-families-nonnegative-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A
{{#concept "partition" Disambiguation="of a closed interval in ℝ" Agda=partition-closed-interval-ℝ}}
of a [closed interval](real-numbers.closed-intervals-real-numbers.md) `[a, b]`
in the [real numbers](real-numbers.dedekind-real-numbers.md) is an
[increasing nonempty array](order-theory.increasing-nonempty-arrays-posets.md)
in `ℝ` whose first element is `a` and whose last element is `b`.

## Definition

```agda
module _
  {l : Level}
  (((a , b) , a≤b) : closed-interval-ℝ l l)
  where

  partition-closed-interval-ℝ : UU (lsuc l)
  partition-closed-interval-ℝ =
    Σ ( increasing-nonempty-array-type-Poset (ℝ-Poset l))
      ( λ u →
        ( head-increasing-nonempty-array-type-Poset (ℝ-Poset l) u ＝ a) ×
        ( last-increasing-nonempty-array-type-Poset (ℝ-Poset l) u ＝ b))
```

## Properties

### The mesh of a partition

```agda
differences-increasing-fin-sequence-ℝ :
  {l : Level} (n : ℕ) →
  increasing-fin-sequence-type-Poset (ℝ-Poset l) (succ-ℕ n) →
  fin-sequence (ℝ⁰⁺ l) n
differences-increasing-fin-sequence-ℝ {l} 0 _ _ = raise-zero-ℝ⁰⁺ l
differences-increasing-fin-sequence-ℝ
  (succ-ℕ n) (u , u₁≤u₂ , is-increasing-tail-u) =
  cons-fin-sequence
    ( n)
    ( nonnegative-diff-leq-ℝ u₁≤u₂)
    ( differences-increasing-fin-sequence-ℝ
      ( n)
      ( tail-fin-sequence (succ-ℕ n) u , is-increasing-tail-u))

module _
  {l : Level}
  ([a,b] : closed-interval-ℝ l l)
  where

  mesh-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ [a,b] → ℝ⁰⁺ l
  mesh-partition-closed-interval-ℝ ((((succ-ℕ n , u) , _) , H) , _) =
    max-fin-sequence-ℝ⁰⁺
      ( n)
      ( differences-increasing-fin-sequence-ℝ n (u , H))

  real-mesh-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ [a,b] → ℝ l
  real-mesh-partition-closed-interval-ℝ =
    real-ℝ⁰⁺ ∘ mesh-partition-closed-interval-ℝ
```

### The trivial partition of a closed interval

```agda
module _
  {l : Level}
  ([a,b]@((a , b) , a≤b) : closed-interval-ℝ l l)
  where

  trivial-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ [a,b]
  trivial-partition-closed-interval-ℝ =
    ( ( ((2 , component-tuple 2 (a ∷ b ∷ empty-tuple)) , star) ,
        a≤b ,
        raise-star) ,
      refl ,
      refl)
```

### The mesh of a partition of `[a, b]` is at most `b - a`

```agda
nonnegative-diff-last-first-increasing-fin-sequence-ℝ :
  {l : Level} (n : ℕ) →
  increasing-fin-sequence-type-Poset (ℝ-Poset l) (succ-ℕ n) →
  ℝ⁰⁺ l
nonnegative-diff-last-first-increasing-fin-sequence-ℝ n (u , H) =
  nonnegative-diff-leq-ℝ
    ( reverses-order-is-increasing-fin-sequence-type-Poset
      ( ℝ-Poset _)
      ( succ-ℕ n)
      ( u)
      ( H)
      ( neg-one-Fin n)
      ( zero-Fin n)
      ( star))

diff-last-first-increasing-fin-sequence-ℝ :
  {l : Level} (n : ℕ) →
  increasing-fin-sequence-type-Poset (ℝ-Poset l) (succ-ℕ n) →
  ℝ l
diff-last-first-increasing-fin-sequence-ℝ n u =
  real-ℝ⁰⁺ (nonnegative-diff-last-first-increasing-fin-sequence-ℝ n u)

abstract
  bound-differences-increasing-fin-sequence-ℝ :
    {l : Level} (n : ℕ)
    (u : increasing-fin-sequence-type-Poset (ℝ-Poset l) (succ-ℕ n))
    (i : Fin n) →
    leq-ℝ
      ( real-ℝ⁰⁺ (differences-increasing-fin-sequence-ℝ n u i))
      ( diff-last-first-increasing-fin-sequence-ℝ n u)
  bound-differences-increasing-fin-sequence-ℝ (succ-ℕ n) (u , H) (inr star) =
    preserves-leq-right-add-ℝ
      ( _)
      ( u (inl (inr star)))
      ( u (zero-Fin (succ-ℕ n)))
      ( reverses-order-is-increasing-fin-sequence-type-Poset
        ( ℝ-Poset _)
        ( succ-ℕ (succ-ℕ n))
        ( u)
        ( H)
        ( inl (inr star))
        ( zero-Fin (succ-ℕ n))
        ( leq-zero-Fin n (inr star)))
  bound-differences-increasing-fin-sequence-ℝ
    (succ-ℕ n) uu@(u , u₁≤u₂ , is-increasing-tail-u) (inl i) =
    transitive-leq-ℝ _ _ _
      ( reverses-leq-left-diff-ℝ
        ( u (zero-Fin (succ-ℕ n)))
        ( u₁≤u₂))
      ( bound-differences-increasing-fin-sequence-ℝ
        ( n)
        ( tail-fin-sequence (succ-ℕ n) u ,
          is-increasing-tail-u)
        ( i))

module _
  {l : Level}
  ([a,b]@((a , b) , a≤b) : closed-interval-ℝ l l)
  where

  abstract
    leq-diff-mesh-partition-closed-interval-ℝ :
      (p : partition-closed-interval-ℝ [a,b]) →
      leq-ℝ⁰⁺
        ( mesh-partition-closed-interval-ℝ [a,b] p)
        ( nonnegative-diff-leq-ℝ a≤b)
    leq-diff-mesh-partition-closed-interval-ℝ
      p@((((succ-ℕ n , u) , _) , H) , head=a , last=b) =
      let
        Δ = differences-increasing-fin-sequence-ℝ n (u , H)
      in
        tr
          ( leq-ℝ (real-mesh-partition-closed-interval-ℝ [a,b] p))
          ( ap-diff-ℝ last=b head=a)
          ( leq-is-least-upper-bound-family-of-elements-Large-Poset
            ( large-poset-ℝ⁰⁺)
            ( Δ)
            ( max-fin-sequence-ℝ⁰⁺ n Δ)
            ( is-least-upper-bound-max-fin-sequence-ℝ⁰⁺ n Δ)
            ( nonnegative-diff-last-first-increasing-fin-sequence-ℝ n (u , H))
            ( bound-differences-increasing-fin-sequence-ℝ n (u , H)))
```

### The standard partition of `[a,b]` with length `n + 2`

```agda
module _
  {l : Level}
  ([a,b]@((a , b) , a≤b) : closed-interval-ℝ l l)
  (n : ℕ)
  where

  hom-fin-sequence-standard-partition-closed-interval-ℝ :
    hom-Poset
      ( opposite-Poset (Fin-Poset (n +ℕ 2)))
      ( ℝ-Poset l)
  hom-fin-sequence-standard-partition-closed-interval-ℝ =
    comp-hom-Poset
      ( opposite-Poset (Fin-Poset (n +ℕ 2)))
      ( ℕ-Poset)
      ( ℝ-Poset l)
      ( comp-hom-Poset
        ( ℕ-Poset)
        ( ℚ-Poset)
        ( ℝ-Poset l)
        ( comp-hom-Poset
          ( ℚ-Poset)
          ( ℚ-Poset)
          ( ℝ-Poset l)
          ( comp-hom-Poset
            ( ℚ-Poset)
            ( ℝ-Poset lzero)
            ( ℝ-Poset l)
            ( comp-hom-Poset
              ( ℝ-Poset lzero)
              ( ℝ-Poset l)
              ( ℝ-Poset l)
              ( hom-poset-left-add-ℝ a)
              ( hom-poset-left-mul-real-ℝ⁰⁺ (nonnegative-diff-leq-ℝ a≤b)))
            ( hom-poset-real-ℚ))
          ( hom-poset-left-mul-rational-ℚ⁰⁺
            ( nonnegative-ℚ⁺ (positive-reciprocal-rational-succ-ℕ n))))
        ( hom-poset-rational-ℕ))
      ( nat-Fin-reverse (n +ℕ 2) ,
        λ i j → reverses-leq-nat-Fin-reverse (n +ℕ 2) j i)

  fin-sequence-standard-partition-closed-interval-ℝ :
    fin-sequence (ℝ l) (n +ℕ 2)
  fin-sequence-standard-partition-closed-interval-ℝ =
    pr1 hom-fin-sequence-standard-partition-closed-interval-ℝ

  abstract
    is-increasing-fin-sequence-standard-partition-closed-interval-ℝ :
      is-increasing-fin-sequence-type-Poset
        ( ℝ-Poset l)
        ( n +ℕ 2)
        ( fin-sequence-standard-partition-closed-interval-ℝ)
    is-increasing-fin-sequence-standard-partition-closed-interval-ℝ =
      is-increasing-reverses-order-fin-sequence-type-Poset
        ( ℝ-Poset l)
        ( n +ℕ 2)
        ( fin-sequence-standard-partition-closed-interval-ℝ)
        ( pr2 hom-fin-sequence-standard-partition-closed-interval-ℝ)

    head-fin-sequence-standard-partition-closed-interval-ℝ :
      head-fin-sequence
        ( succ-ℕ n)
        ( fin-sequence-standard-partition-closed-interval-ℝ) ＝
      a
    head-fin-sequence-standard-partition-closed-interval-ℝ =
      equational-reasoning
        a +ℝ (b -ℝ a) *ℝ real-ℚ (reciprocal-rational-succ-ℕ n *ℚ zero-ℚ)
        ＝ a +ℝ (b -ℝ a) *ℝ zero-ℝ
          by ap-add-ℝ refl (ap-mul-ℝ refl (ap real-ℚ (right-zero-law-mul-ℚ _)))
        ＝ a +ℝ raise-zero-ℝ l
          by ap-add-ℝ refl (eq-right-zero-law-mul-ℝ _)
        ＝ a
          by right-raise-zero-law-add-ℝ a

    last-fin-sequence-standard-partition-closed-interval-ℝ :
      last-fin-sequence
        ( succ-ℕ n)
        ( fin-sequence-standard-partition-closed-interval-ℝ) ＝
      b
    last-fin-sequence-standard-partition-closed-interval-ℝ =
      let
        1/⟨n+1⟩ = reciprocal-rational-succ-ℕ n
      in
        equational-reasoning
          ( a) +ℝ
          ( ( b -ℝ a) *ℝ
            ( real-ℚ
              ( 1/⟨n+1⟩ *ℚ
                rational-ℕ (nat-Fin-reverse (n +ℕ 2) (zero-Fin (succ-ℕ n))))))
          ＝ a +ℝ ((b -ℝ a) *ℝ (real-ℚ (1/⟨n+1⟩ *ℚ rational-ℕ (succ-ℕ n))))
            by
              ap
                ( λ k → a +ℝ (b -ℝ a) *ℝ real-ℚ (1/⟨n+1⟩ *ℚ rational-ℕ k))
                ( nat-reverse-zero-Fin (succ-ℕ n))
          ＝ a +ℝ ((b -ℝ a) *ℝ one-ℝ)
            by
              ap
                ( λ q → a +ℝ (b -ℝ a) *ℝ real-ℚ⁺ q)
                ( left-inverse-law-mul-ℚ⁺
                  ( positive-rational-ℕ⁺ (succ-nonzero-ℕ' n)))
          ＝ a +ℝ (b -ℝ a)
            by ap-add-ℝ refl (right-unit-law-mul-ℝ (b -ℝ a))
          ＝ b
            by eq-sim-ℝ (add-right-diff-ℝ a b)

  standard-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ [a,b]
  standard-partition-closed-interval-ℝ =
    ( ( ((n +ℕ 2 , fin-sequence-standard-partition-closed-interval-ℝ) , star) ,
        is-increasing-fin-sequence-standard-partition-closed-interval-ℝ) ,
      head-fin-sequence-standard-partition-closed-interval-ℝ ,
      last-fin-sequence-standard-partition-closed-interval-ℝ)
```

## External links

- [Partition of an interval](https://en.wikipedia.org/wiki/Partition_of_an_interval)
  on Wikipedia
