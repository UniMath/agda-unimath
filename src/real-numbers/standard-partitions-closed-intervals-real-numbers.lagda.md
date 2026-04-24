# Standard partitions of closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.standard-partitions-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.archimedean-property-positive-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-homotopies-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.abelian-groups

open import lists.finite-sequences

open import order-theory.increasing-finite-sequences-posets
open import order-theory.large-posets
open import order-theory.opposite-posets
open import order-theory.order-preserving-maps-posets

open import real-numbers.addition-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maximum-finite-families-nonnegative-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.partitions-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "standard partition" Disambiguation="of length n+2 of a closed interval in ℝ" Agda=standard-partition-closed-interval-ℝ}}
of a [closed interval](real-numbers.closed-intervals-real-numbers.md) `[a, b]`
in the [real numbers](real-numbers.dedekind-real-numbers.md) with `n + 2`
elements is the
[partition](real-numbers.partitions-closed-intervals-real-numbers.md)
`p_i := a + (b - a) i /(n + 1)`, where `i` ranges from `0` to `n + 1`.

## Definition

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

## Properties

### The mesh of the standard partition of `[a, b]` with length `n + 2` is `(b - a) / (n + 1)`

```agda
module _
  {l : Level}
  ([a,b]@((a , b) , a≤b) : closed-interval-ℝ l l)
  (n : ℕ)
  where

  abstract
    compute-diffs-standard-partition-closed-interval-ℝ :
      (i : Fin (succ-ℕ n)) →
      diffs-partition-closed-interval-ℝ
        ( [a,b])
        ( standard-partition-closed-interval-ℝ [a,b] n)
        ( i) ＝
      ( ( nonnegative-diff-leq-ℝ a≤b) *ℝ⁰⁺
        ( nonnegative-real-ℚ⁺ (positive-reciprocal-rational-succ-ℕ n)))
    compute-diffs-standard-partition-closed-interval-ℝ i =
      let
        1/⟨n+1⟩ = reciprocal-rational-succ-ℕ n
      in
        eq-ℝ⁰⁺ _ _
          ( equational-reasoning
            width-closed-interval-ℝ
              ( fin-sequence-closed-interval-partition-closed-interval-ℝ
                ( [a,b])
                ( standard-partition-closed-interval-ℝ [a,b] n)
                ( i))
            ＝
              ( fin-sequence-standard-partition-closed-interval-ℝ
                ( [a,b])
                ( n)
                ( inl-Fin (succ-ℕ n) i)) -ℝ
              ( fin-sequence-standard-partition-closed-interval-ℝ
                ( [a,b])
                ( n)
                ( skip-zero-Fin (succ-ℕ n) i))
              by
                ap
                  ( width-closed-interval-ℝ)
                  ( htpy-closed-intervals-increasing-fin-sequence-type-Poset'
                    ( ℝ-Poset l)
                    ( succ-ℕ n)
                    ( increasing-real-fin-sequence-partition-closed-interval-ℝ
                      ( [a,b])
                      ( standard-partition-closed-interval-ℝ [a,b] n))
                    ( i))
            ＝
              ( ( b -ℝ a) *ℝ
                ( real-ℚ
                  ( ( 1/⟨n+1⟩) *ℚ
                    ( rational-ℕ
                      ( nat-Fin-reverse (n +ℕ 2) (inl-Fin (succ-ℕ n) i)))))) -ℝ
              ( ( b -ℝ a) *ℝ
                ( real-ℚ
                  ( ( 1/⟨n+1⟩) *ℚ
                    ( rational-ℕ
                      ( nat-Fin-reverse
                        ( n +ℕ 2)
                        ( skip-zero-Fin (succ-ℕ n) i))))))
              by eq-sim-ℝ (diff-left-add-ℝ a _ _)
            ＝ (b -ℝ a) *ℝ (real-ℚ _ -ℝ real-ℚ _)
              by
                inv
                  ( left-distributive-mul-diff-ℝ (b -ℝ a) (real-ℚ _) (real-ℚ _))
            ＝ (b -ℝ a) *ℝ real-ℚ (_ -ℚ _)
              by ap-mul-ℝ refl (diff-real-ℚ _ _)
            ＝ (b -ℝ a) *ℝ real-ℚ (1/⟨n+1⟩ *ℚ (_ -ℚ _))
              by
                ap-mul-ℝ
                  ( refl)
                  ( ap
                    ( real-ℚ)
                    ( inv (left-distributive-mul-diff-ℚ 1/⟨n+1⟩ _ _)))
            ＝
              ( b -ℝ a) *ℝ
              ( real-ℚ
                ( ( 1/⟨n+1⟩) *ℚ
                  ( ( rational-ℕ
                      ( succ-ℕ
                        ( nat-Fin-reverse
                          ( n +ℕ 2)
                          ( skip-zero-Fin (succ-ℕ n) i)))) -ℚ
                    ( rational-ℕ
                      ( nat-Fin-reverse
                        ( n +ℕ 2)
                        ( skip-zero-Fin (succ-ℕ n) i))))))
              by
                ap-mul-ℝ
                  ( refl)
                  ( ap
                    ( real-ℚ)
                    ( ap-mul-ℚ
                      ( refl)
                      ( ap-diff-ℚ
                        ( ap
                          ( rational-ℕ)
                          ( compute-nat-reverse-inl-Fin (succ-ℕ n) i))
                        ( refl))))
            ＝
              ( b -ℝ a) *ℝ
              ( real-ℚ
                ( ( 1/⟨n+1⟩) *ℚ
                  ( ( succ-ℚ
                      ( rational-ℕ
                        ( nat-Fin-reverse
                          ( n +ℕ 2)
                          ( skip-zero-Fin (succ-ℕ n) i)))) -ℚ
                    ( rational-ℕ
                      ( nat-Fin-reverse
                        ( n +ℕ 2)
                        ( skip-zero-Fin (succ-ℕ n) i))))))
              by
                ap-mul-ℝ
                  ( refl)
                  ( ap
                    ( real-ℚ)
                    ( ap-mul-ℚ refl (ap-diff-ℚ (inv (succ-rational-ℕ _)) refl)))
            ＝ (b -ℝ a) *ℝ real-ℚ (1/⟨n+1⟩ *ℚ one-ℚ)
              by ap-mul-ℝ refl (ap real-ℚ (ap-mul-ℚ refl (diff-succ-ℚ _)))
            ＝ (b -ℝ a) *ℝ real-ℚ 1/⟨n+1⟩
              by ap-mul-ℝ refl (ap real-ℚ (right-unit-law-mul-ℚ _)))

    mesh-standard-partition-closed-interval-ℝ :
      mesh-partition-closed-interval-ℝ
        ( [a,b])
        ( standard-partition-closed-interval-ℝ [a,b] n) ＝
      nonnegative-width-closed-interval-ℝ [a,b] *ℝ⁰⁺
      nonnegative-real-ℚ⁺ (positive-reciprocal-rational-succ-ℕ n)
    mesh-standard-partition-closed-interval-ℝ =
      ( action-htpy-function
        ( max-fin-sequence-ℝ⁰⁺ (succ-ℕ n))
        ( compute-diffs-standard-partition-closed-interval-ℝ)) ∙
      ( max-constant-fin-sequence-ℝ⁰⁺ n _)
```

### For any positive `ε` and interval `[a, b]`, there is a partition of `[a, b]` with mesh at most `ε`

```agda
module _
  {l : Level}
  ([a,b]@((a , b) , a≤b) : closed-interval-ℝ l l)
  (ε : ℚ⁺)
  where

  abstract
    exists-partition-mesh-bound-closed-interval-ℝ :
      exists
        ( partition-closed-interval-ℝ [a,b])
        ( λ p →
          leq-prop-ℝ
            ( real-mesh-partition-closed-interval-ℝ [a,b] p)
            ( real-ℚ⁺ ε))
    exists-partition-mesh-bound-closed-interval-ℝ =
      let
        open do-syntax-trunc-Prop (∃ (partition-closed-interval-ℝ [a,b]) _)
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in do
        (q , b-a<q) ← exists-greater-positive-rational-ℝ (b -ℝ a)
        (n⁺ , q<n⁺ε) ← archimedean-property-ℚ⁺ ε q
        let n = nat-ℕ⁺ n⁺
        intro-exists
          ( standard-partition-closed-interval-ℝ [a,b] n)
          ( chain-of-inequalities
            real-mesh-partition-closed-interval-ℝ
              ( [a,b])
              ( standard-partition-closed-interval-ℝ [a,b] n)
            ≤ (b -ℝ a) *ℝ real-ℚ (reciprocal-rational-succ-ℕ n)
              by
                leq-eq-ℝ
                  ( ap
                    ( real-ℝ⁰⁺)
                    ( mesh-standard-partition-closed-interval-ℝ [a,b] n))
            ≤ ( real-ℚ⁺ (positive-rational-ℕ⁺ n⁺ *ℚ⁺ ε)) *ℝ
              ( real-ℚ (reciprocal-rational-succ-ℕ n))
              by
                preserves-leq-right-mul-ℝ⁰⁺
                  ( nonnegative-real-ℚ⁺ (positive-reciprocal-rational-succ-ℕ n))
                  ( transitive-leq-ℝ
                    ( b -ℝ a)
                    ( real-ℚ⁺ q)
                    ( real-ℚ⁺ (positive-rational-ℕ⁺ n⁺ *ℚ⁺ ε))
                    ( preserves-leq-real-ℚ (leq-le-ℚ q<n⁺ε))
                    ( leq-le-ℝ b-a<q))
            ≤ ( real-ℚ⁺ (positive-rational-ℕ⁺ (succ-nonzero-ℕ n⁺) *ℚ⁺ ε)) *ℝ
              ( real-ℚ (reciprocal-rational-succ-ℕ n))
              by
                preserves-leq-right-mul-ℝ⁰⁺
                  ( nonnegative-real-ℚ⁺ (positive-reciprocal-rational-succ-ℕ n))
                  ( preserves-leq-real-ℚ
                    ( preserves-leq-right-mul-ℚ⁺
                      ( ε)
                      ( _)
                      ( _)
                      ( preserves-leq-rational-ℕ (succ-leq-ℕ n))))
            ≤ real-ℚ⁺
                ( ( positive-rational-ℕ⁺ (succ-nonzero-ℕ n⁺) *ℚ⁺ ε) *ℚ⁺
                  ( positive-reciprocal-rational-succ-ℕ n))
              by leq-eq-ℝ (mul-real-ℚ _ _)
            ≤ real-ℚ⁺ ε
              by
                leq-eq-ℝ
                  ( ap
                    ( real-ℚ⁺)
                    ( is-identity-left-conjugation-Ab
                      ( abelian-group-mul-ℚ⁺)
                      ( positive-rational-ℕ⁺ (succ-nonzero-ℕ n⁺))
                      ( ε))))
```
