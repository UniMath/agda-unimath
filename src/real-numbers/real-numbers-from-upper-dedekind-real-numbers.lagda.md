# Real numbers from upper Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.real-numbers-from-upper-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.complements-subtypes
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

Given an
[upper Dedekind real number](real-numbers.upper-dedekind-real-numbers.md) `x`,
we can convert `x` to a
[Dedekind real number](real-numbers.dedekind-real-numbers.md) if and only if the
[complement](foundation.complements-subtypes.md) of the cut of `x` is
[inhabited](foundation.inhabited-subtypes.md) and for any `p q : ℚ` with
`p < q`, `p` is in the [complement](foundation.complements-subtypes.md) of the
cut of `x` [or](foundation.disjunction.md) `q` is in the cut of `x`.

## Definition

```agda
module _
  {l : Level} (x : upper-ℝ l)
  (L :
    (p q : ℚ) → le-ℚ p q →
    type-disjunction-Prop (¬' (cut-upper-ℝ x p)) (cut-upper-ℝ x q))
  (I : is-inhabited-subtype (complement-subtype (cut-upper-ℝ x)))
  where

  lower-cut-real-upper-ℝ : subtype l ℚ
  lower-cut-real-upper-ℝ p =
    ∃ ℚ (λ q → le-ℚ-Prop p q ∧ ¬' (cut-upper-ℝ x q))

  abstract
    is-inhabited-lower-cut-real-upper-ℝ :
      is-inhabited-subtype lower-cut-real-upper-ℝ
    is-inhabited-lower-cut-real-upper-ℝ =
      let
        open
          do-syntax-trunc-Prop
            (is-inhabited-subtype-Prop
              lower-cut-real-upper-ℝ)
      in do
        (p , p∉U) ← I
        (r , r<p) ← exists-lesser-ℚ p
        intro-exists r (intro-exists p (r<p , p∉U))

    is-rounded-lower-cut-real-upper-ℝ :
      (q : ℚ) →
      is-in-subtype lower-cut-real-upper-ℝ q ↔
      exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-real-upper-ℝ r)
    pr1 (is-rounded-lower-cut-real-upper-ℝ q) q∈L =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-real-upper-ℝ r))
      in do
        (r , q<r , r∉U) ← q∈L
        intro-exists
          ( mediant-ℚ q r)
          ( le-left-mediant-ℚ q r q<r ,
            intro-exists r (le-right-mediant-ℚ q r q<r , r∉U))
    pr2 (is-rounded-lower-cut-real-upper-ℝ q) ∃r =
      let open do-syntax-trunc-Prop (lower-cut-real-upper-ℝ q)
      in do
        (r , q<r , r∈L) ← ∃r
        (s , r<s , s∉U) ← r∈L
        intro-exists s (transitive-le-ℚ q r s r<s q<r , s∉U)

  lower-real-real-upper-ℝ : lower-ℝ l
  lower-real-real-upper-ℝ =
    ( lower-cut-real-upper-ℝ ,
      is-inhabited-lower-cut-real-upper-ℝ ,
      is-rounded-lower-cut-real-upper-ℝ)

  abstract
    is-disjoint-cut-real-upper-ℝ :
      disjoint-subtype
        ( lower-cut-real-upper-ℝ)
        ( cut-upper-ℝ x)
    is-disjoint-cut-real-upper-ℝ q (q∈L , q∈U) =
      let open do-syntax-trunc-Prop empty-Prop
      in do
        (r , q<r , r∉U) ← q∈L
        r∉U (is-in-cut-le-ℚ-upper-ℝ x q r q<r q∈U)

    is-located-cut-real-upper-ℝ :
      (p q : ℚ) → le-ℚ p q →
      type-disjunction-Prop (lower-cut-real-upper-ℝ p) (cut-upper-ℝ x q)
    is-located-cut-real-upper-ℝ p q p<q =
      let
        r = mediant-ℚ p q
      in
        elim-disjunction
          (lower-cut-real-upper-ℝ p ∨ cut-upper-ℝ x q)
          ( λ r∉U →
            inl-disjunction (intro-exists r (le-left-mediant-ℚ p q p<q , r∉U)))
          ( inr-disjunction)
          ( L r q (le-right-mediant-ℚ p q p<q))

  real-upper-ℝ : ℝ l
  real-upper-ℝ =
    real-lower-upper-ℝ
      ( lower-real-real-upper-ℝ)
      ( x)
      ( is-disjoint-cut-real-upper-ℝ)
      ( is-located-cut-real-upper-ℝ)
```

## See also

- [Real numbers from lower Dedekind real numbers](real-numbers.real-numbers-from-lower-dedekind-real-numbers.md)
