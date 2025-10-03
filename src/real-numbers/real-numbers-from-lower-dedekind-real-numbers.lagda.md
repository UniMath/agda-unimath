# Real numbers from lower Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.real-numbers-from-lower-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
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
open import foundation.function-types
open import foundation.functoriality-disjunction
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

Given a
[lower Dedekind real number](real-numbers.lower-dedekind-real-numbers.md) `x`,
we can convert `x` to a
[Dedekind real number](real-numbers.dedekind-real-numbers.md) if and only if the
[complement](foundation.complements-subtypes.md) of the cut of `x` is
[inhabited](foundation.inhabited-subtypes.md) and for any `p q : ℚ` with
`p < q`, `p` is in the cut of `x` [or](foundation.disjunction.md) `q` is in the
[complement](foundation.complements-subtypes.md) of the cut of `x`.

## Definition

```agda
module _
  {l : Level} (x : lower-ℝ l)
  (L :
    (p q : ℚ) → le-ℚ p q →
    type-disjunction-Prop (cut-lower-ℝ x p) (¬' (cut-lower-ℝ x q)))
  (I : is-inhabited-subtype (complement-subtype (cut-lower-ℝ x)))
  where

  upper-cut-real-lower-ℝ : subtype l ℚ
  upper-cut-real-lower-ℝ q =
    ∃ ℚ (λ p → le-ℚ-Prop p q ∧ ¬' (cut-lower-ℝ x p))

  abstract
    is-inhabited-upper-cut-real-lower-ℝ :
      is-inhabited-subtype upper-cut-real-lower-ℝ
    is-inhabited-upper-cut-real-lower-ℝ =
      let
        open
          do-syntax-trunc-Prop
            (is-inhabited-subtype-Prop
              upper-cut-real-lower-ℝ)
      in do
        (p , p∉L) ← I
        (q , p<q) ← exists-greater-ℚ p
        intro-exists q (intro-exists p (p<q , p∉L))

    is-rounded-upper-cut-real-lower-ℝ :
      (q : ℚ) →
      is-in-subtype upper-cut-real-lower-ℝ q ↔
      exists
        ( ℚ)
        ( λ p →
          le-ℚ-Prop p q ∧ upper-cut-real-lower-ℝ p)
    pr1 (is-rounded-upper-cut-real-lower-ℝ q) q∈U =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ (λ p → le-ℚ-Prop p q ∧ upper-cut-real-lower-ℝ p))
      in do
        (p , p<q , p∉L) ← q∈U
        intro-exists
          ( mediant-ℚ p q)
          ( le-right-mediant-ℚ p q p<q ,
            intro-exists p (le-left-mediant-ℚ p q p<q , p∉L))
    pr2 (is-rounded-upper-cut-real-lower-ℝ q) ∃p =
      let open do-syntax-trunc-Prop (upper-cut-real-lower-ℝ q)
      in do
        (p , p<q , p∈U) ← ∃p
        (r , r<p , r∉L) ← p∈U
        intro-exists r (transitive-le-ℚ r p q p<q r<p , r∉L)

  upper-real-real-lower-ℝ : upper-ℝ l
  upper-real-real-lower-ℝ =
    ( upper-cut-real-lower-ℝ ,
      is-inhabited-upper-cut-real-lower-ℝ ,
      is-rounded-upper-cut-real-lower-ℝ)

  abstract
    is-disjoint-cut-real-lower-ℝ :
      disjoint-subtype
        ( cut-lower-ℝ x)
        ( upper-cut-real-lower-ℝ)
    is-disjoint-cut-real-lower-ℝ q (q∈L , q∈U) =
      let open do-syntax-trunc-Prop empty-Prop
      in do
        (r , r<q , r∉L) ← q∈U
        r∉L (is-in-cut-le-ℚ-lower-ℝ x r q r<q q∈L)

    is-located-cut-real-lower-ℝ :
      (p q : ℚ) → le-ℚ p q →
      type-disjunction-Prop
        ( cut-lower-ℝ x p)
        ( upper-cut-real-lower-ℝ q)
    is-located-cut-real-lower-ℝ p q p<q =
      let
        r = mediant-ℚ p q
      in
        map-disjunction
          ( id)
          ( λ r∉L → intro-exists r ( le-right-mediant-ℚ p q p<q , r∉L))
          ( L p r (le-left-mediant-ℚ p q p<q))

  real-lower-ℝ : ℝ l
  real-lower-ℝ =
    real-lower-upper-ℝ
      ( x)
      ( upper-real-real-lower-ℝ)
      ( is-disjoint-cut-real-lower-ℝ)
      ( is-located-cut-real-lower-ℝ)
```

## See also

- [Real numbers from upper Dedekind real numbers](real-numbers.real-numbers-from-upper-dedekind-real-numbers.md)
