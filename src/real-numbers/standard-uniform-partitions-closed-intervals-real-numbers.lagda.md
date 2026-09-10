# The standard uniform partitions of closed intervals in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.standard-uniform-partitions-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.null-homotopic-maps
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.weakly-constant-maps

open import group-theory.abelian-groups

open import lists.arrays
open import lists.finite-sequences
open import lists.nonempty-arrays

open import order-theory.increasing-finite-sequences-posets
open import order-theory.increasing-nonempty-arrays-posets

open import real-numbers.addition-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.large-additive-group-of-real-numbers
open import real-numbers.maximum-finite-families-nonnegative-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.partitions-closed-intervals-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.uniform-partitions-closed-intervals-real-numbers
open import real-numbers.unit-fractions-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `n` and a
[closed interval](real-numbers.closed-intervals-real-numbers.md) `[a, b]` in the
[real numbers](real-numbers.dedekind-real-numbers.md), the
{{#concept "standard uniform partition" Disambiguation="of a given length closed interval in the real numbers" Agda=standard-uniform-partition-closed-interval-ℝ}}
of `[a, b]` contains `n + 1` intervals, each of width `(b - a) / (n + 1)`.

## Definition

```agda
module _
  {l : Level}
  ([a,b]@((a , b) , a≤b) : closed-interval-ℝ l l)
  (n : ℕ)
  (let 1/⟨n+1⟩ = reciprocal-real-succ-ℕ n)
  where

  fin-sequence-standard-uniform-partition-closed-interval-ℝ :
    fin-sequence (ℝ l) (n +ℕ 2)
  fin-sequence-standard-uniform-partition-closed-interval-ℝ i =
    a +ℝ (b -ℝ a) *ℝ 1/⟨n+1⟩ *ℝ real-ℕ (nat-Fin (n +ℕ 2) i)

  abstract
    is-increasing-fin-sequence-standard-uniform-partition-closed-interval-ℝ :
      is-increasing-fin-sequence-type-Poset
        ( ℝ-Poset l)
        ( n +ℕ 2)
        ( fin-sequence-standard-uniform-partition-closed-interval-ℝ)
    is-increasing-fin-sequence-standard-uniform-partition-closed-interval-ℝ
      i j i≤j =
      preserves-leq-left-add-ℝ a _ _
        ( preserves-leq-left-mul-ℝ⁰⁺
          ( nonnegative-diff-leq-ℝ a≤b *ℝ⁰⁺
            nonnegative-ℝ⁺ (positive-reciprocal-real-succ-ℕ n))
          ( preserves-leq-real-ℕ (preserves-leq-nat-Fin (n +ℕ 2) {i} {j} i≤j)))

  array-standard-uniform-partition-closed-interval-ℝ : array (ℝ l)
  array-standard-uniform-partition-closed-interval-ℝ =
    ( n +ℕ 2 , fin-sequence-standard-uniform-partition-closed-interval-ℝ)

  nonempty-array-standard-uniform-partition-closed-interval-ℝ :
    nonempty-array (ℝ l)
  nonempty-array-standard-uniform-partition-closed-interval-ℝ =
    ( array-standard-uniform-partition-closed-interval-ℝ ,
      star)

  increasing-nonempty-array-standard-uniform-partition-closed-interval-ℝ :
    increasing-nonempty-array-type-Poset (ℝ-Poset l)
  increasing-nonempty-array-standard-uniform-partition-closed-interval-ℝ =
    ( nonempty-array-standard-uniform-partition-closed-interval-ℝ ,
      is-increasing-fin-sequence-standard-uniform-partition-closed-interval-ℝ)

  abstract
    is-lower-bound-last-fin-sequence-standard-uniform-partition-closed-interval-ℝ :
      last-fin-sequence
        ( succ-ℕ n)
        ( fin-sequence-standard-uniform-partition-closed-interval-ℝ) ＝
      lower-bound-closed-interval-ℝ [a,b]
    is-lower-bound-last-fin-sequence-standard-uniform-partition-closed-interval-ℝ =
      eq-sim-ℝ
        ( similarity-reasoning-ℝ
          ( a) +ℝ
          ( (b -ℝ a) *ℝ
            1/⟨n+1⟩ *ℝ
            real-ℕ (nat-Fin (n +ℕ 2) (zero-Fin (succ-ℕ n))))
          ~ℝ a +ℝ (b -ℝ a) *ℝ 1/⟨n+1⟩ *ℝ zero-ℝ
            by
              sim-eq-ℝ
                ( ap-add-ℝ
                  ( refl)
                  ( ap-mul-ℝ refl (ap real-ℕ (nat-zero-Fin (n +ℕ 2)))))
          ~ℝ a +ℝ zero-ℝ
            by preserves-sim-left-add-ℝ a _ _ (right-zero-law-mul-ℝ _)
          ~ℝ a
            by sim-eq-ℝ (right-unit-law-add-ℝ a))

    is-upper-bound-head-fin-sequence-standard-uniform-partition-closed-interval-ℝ :
      head-fin-sequence
        ( succ-ℕ n)
        ( fin-sequence-standard-uniform-partition-closed-interval-ℝ) ＝
      b
    is-upper-bound-head-fin-sequence-standard-uniform-partition-closed-interval-ℝ =
      equational-reasoning
        a +ℝ (b -ℝ a) *ℝ 1/⟨n+1⟩ *ℝ real-ℕ (succ-ℕ n)
        ＝ a +ℝ (b -ℝ a) *ℝ (1/⟨n+1⟩ *ℝ real-ℕ (succ-ℕ n))
          by ap-add-ℝ refl (associative-mul-ℝ _ _ _)
        ＝ a +ℝ (b -ℝ a) *ℝ one-ℝ
          by
            ap-add-ℝ
              ( refl)
              ( ap-mul-ℝ refl (left-inverse-law-reciprocal-real-succ-ℕ n))
        ＝ a +ℝ (b -ℝ a)
          by ap-add-ℝ refl (right-unit-law-mul-ℝ _)
        ＝ b
          by eq-sim-ℝ (cancel-right-conjugation-ℝ a b)

  partition-standard-uniform-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ [a,b]
  partition-standard-uniform-partition-closed-interval-ℝ =
    ( increasing-nonempty-array-standard-uniform-partition-closed-interval-ℝ ,
      is-lower-bound-last-fin-sequence-standard-uniform-partition-closed-interval-ℝ ,
      is-upper-bound-head-fin-sequence-standard-uniform-partition-closed-interval-ℝ)

  mesh-standard-uniform-partition-closed-interval-ℝ : ℝ⁰⁺ l
  mesh-standard-uniform-partition-closed-interval-ℝ =
    nonnegative-width-closed-interval-ℝ [a,b] *ℝ⁰⁺
    nonnegative-reciprocal-real-succ-ℕ n

  abstract
    compute-diffs-partition-standard-uniform-partition-closed-interval-ℝ :
      (i : Fin (succ-ℕ n)) →
      diffs-partition-closed-interval-ℝ
        ( [a,b])
        ( partition-standard-uniform-partition-closed-interval-ℝ)
        ( i) ＝
      nonnegative-width-closed-interval-ℝ [a,b] *ℝ⁰⁺
      nonnegative-reciprocal-real-succ-ℕ n
    compute-diffs-partition-standard-uniform-partition-closed-interval-ℝ i =
      let
        iℕ = nat-Fin (n +ℕ 2) (inl-Fin (succ-ℕ n) i)
        jℕ = nat-Fin (n +ℕ 2) (inr-Fin (succ-ℕ n) i)
      in
        eq-ℝ⁰⁺ _ _
          ( equational-reasoning
            ( a +ℝ (b -ℝ a) *ℝ 1/⟨n+1⟩ *ℝ real-ℕ jℕ) -ℝ
            ( a +ℝ (b -ℝ a) *ℝ 1/⟨n+1⟩ *ℝ real-ℕ iℕ)
            ＝
              ((b -ℝ a) *ℝ 1/⟨n+1⟩ *ℝ real-ℕ jℕ) -ℝ
              ((b -ℝ a) *ℝ 1/⟨n+1⟩ *ℝ real-ℕ iℕ)
              by right-subtraction-left-add-Ab (ab-add-ℝ l) _ _ _
            ＝
              ((b -ℝ a) *ℝ 1/⟨n+1⟩) *ℝ (real-ℕ jℕ -ℝ real-ℕ iℕ)
              by
                inv
                  ( left-distributive-mul-diff-ℝ
                    ( (b -ℝ a) *ℝ 1/⟨n+1⟩)
                    ( real-ℕ jℕ)
                    ( real-ℕ iℕ))
            ＝
              ((b -ℝ a) *ℝ 1/⟨n+1⟩) *ℝ (real-ℕ (succ-ℕ iℕ) -ℝ real-ℕ iℕ)
              by
                ap-mul-ℝ
                  { l1 = l}
                  ( refl)
                  { l2 = lzero}
                  ( ap-diff-ℝ (ap real-ℕ (nat-inr-Fin (succ-ℕ n) i)) refl)
            ＝
              ( (b -ℝ a) *ℝ 1/⟨n+1⟩) *ℝ
              ( (real-ℕ iℕ +ℝ one-ℝ) -ℝ real-ℕ iℕ)
              by
                ap-mul-ℝ
                  { l1 = l}
                  ( refl)
                  { l2 = lzero}
                  ( ap-diff-ℝ (inv (add-real-ℕ iℕ 1)) refl)
            ＝ ((b -ℝ a) *ℝ 1/⟨n+1⟩) *ℝ one-ℝ
              by
                ap-mul-ℝ
                  { l1 = l}
                  ( refl)
                  { l2 = lzero}
                  ( eq-sim-ℝ (cancel-left-conjugation-ℝ (real-ℕ iℕ) one-ℝ))
            ＝ (b -ℝ a) *ℝ 1/⟨n+1⟩
              by right-unit-law-mul-ℝ _)

  is-null-homotopic-map-diffs-partition-standard-uniform-partition-closed-interval-ℝ :
    is-null-homotopic-map
      ( diffs-partition-closed-interval-ℝ
        ( [a,b])
        ( partition-standard-uniform-partition-closed-interval-ℝ))
  is-null-homotopic-map-diffs-partition-standard-uniform-partition-closed-interval-ℝ =
    ( mesh-standard-uniform-partition-closed-interval-ℝ ,
      compute-diffs-partition-standard-uniform-partition-closed-interval-ℝ)

  is-uniform-partition-standard-uniform-partition-closed-interval-ℝ :
    is-uniform-partition-closed-interval-ℝ
      ( [a,b])
      ( partition-standard-uniform-partition-closed-interval-ℝ)
  is-uniform-partition-standard-uniform-partition-closed-interval-ℝ =
    is-weakly-constant-map-is-null-homotopic-map
      ( left-comp-is-null-homotopic-map
        ( real-ℝ⁰⁺)
        ( is-null-homotopic-map-diffs-partition-standard-uniform-partition-closed-interval-ℝ))

  standard-uniform-partition-closed-interval-ℝ :
    uniform-partition-closed-interval-ℝ [a,b]
  standard-uniform-partition-closed-interval-ℝ =
    ( partition-standard-uniform-partition-closed-interval-ℝ ,
      is-uniform-partition-standard-uniform-partition-closed-interval-ℝ)

  abstract
    compute-mesh-standard-uniform-partition-closed-interval-ℝ :
      mesh-uniform-partition-closed-interval-ℝ
        ( [a,b])
        ( standard-uniform-partition-closed-interval-ℝ) ＝
      mesh-standard-uniform-partition-closed-interval-ℝ
    compute-mesh-standard-uniform-partition-closed-interval-ℝ =
      max-weakly-constant-fin-sequence-ℝ⁰⁺
        ( succ-ℕ n)
        ( diffs-partition-closed-interval-ℝ
          ( [a,b])
          ( partition-standard-uniform-partition-closed-interval-ℝ))
        ( is-weakly-constant-fin-sequence-nonnegative-width-closed-interval-uniform-partition-closed-interval-ℝ
          ( [a,b])
          ( standard-uniform-partition-closed-interval-ℝ))
        ( neg-one-Fin n) ∙
      compute-diffs-partition-standard-uniform-partition-closed-interval-ℝ
        ( neg-one-Fin n)
```

## Properties

### Every nonempty uniform partition of a closed interval is standard

This has yet to be proven.
