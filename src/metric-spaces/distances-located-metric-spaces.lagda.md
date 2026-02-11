# Distances in located metric spaces

```agda
module metric-spaces.distances-located-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.coproduct-types
open import foundation.negation
open import elementary-number-theory.rational-numbers
open import foundation.dependent-pair-types
open import real-numbers.upper-dedekind-real-numbers
open import foundation.existential-quantification
open import real-numbers.dedekind-real-numbers
open import foundation.empty-types
open import foundation.propositional-truncations
open import real-numbers.nonnegative-real-numbers
open import foundation.logical-equivalences
open import real-numbers.rational-real-numbers
open import real-numbers.inequality-real-numbers
open import elementary-number-theory.inequality-rational-numbers
open import real-numbers.real-numbers-from-upper-dedekind-real-numbers
open import foundation.disjunction
open import metric-spaces.metric-spaces
open import foundation.functoriality-disjunction
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import metric-spaces.located-metric-spaces
open import metric-spaces.elements-at-bounded-distance-metric-spaces
```

</details>

## Idea

If two elements of a
[located metric space](metric-spaces.located-metric-spaces.md) are at
[bounded distance](metric-spaces.elements-at-bounded-distance-metric-spaces.md),
there is a [real number](real-numbers.dedekind-real-numbers.md) corresponding to
their distance `d`.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2) (L : is-located-Metric-Space M)
  (x y : type-Metric-Space M) (B : bounded-dist-Metric-Space M x y)
  where

  abstract
    is-located-dist-located-Metric-Space :
      (p q : ℚ) → le-ℚ p q →
      type-disjunction-Prop
        ( ¬' (cut-upper-ℝ (upper-real-dist-Metric-Space M x y B) p))
        ( cut-upper-ℝ (upper-real-dist-Metric-Space M x y B) q)
    is-located-dist-located-Metric-Space p q p<q =
      rec-coproduct
        ( λ 0<p →
          let
            r = mediant-ℚ p q
            p⁺ = (p , is-positive-le-zero-ℚ 0<p)
            p<r = le-left-mediant-ℚ p<q
            r⁺ =
              ( r ,
                is-positive-le-zero-ℚ (transitive-le-ℚ zero-ℚ p r p<r 0<p))
          in
            map-disjunction
              ( λ ¬Npxy p∈U →
                let open do-syntax-trunc-Prop empty-Prop
                in do
                  ((ε⁺@(ε , _) , Nεxy) , ε<p) ← p∈U
                  ¬Npxy
                    ( monotonic-neighborhood-Metric-Space M x y ε⁺ p⁺ ε<p Nεxy))
              ( λ Nrxy → intro-exists (r⁺ , Nrxy) (le-right-mediant-ℚ p<q))
              ( L x y p⁺ r⁺ p<r))
        ( λ p≤0 →
          inl-disjunction
            ( leq-zero-not-in-cut-upper-real-dist-Metric-Space M x y B p p≤0))
        ( decide-le-leq-ℚ zero-ℚ p)

  opaque
    real-dist-located-Metric-Space : ℝ l2
    real-dist-located-Metric-Space =
      real-upper-ℝ
        ( upper-real-dist-Metric-Space M x y B)
        ( is-located-dist-located-Metric-Space)
        ( intro-exists
          ( zero-ℚ)
          ( leq-zero-not-in-cut-upper-real-dist-Metric-Space M x y B zero-ℚ
            ( refl-leq-ℚ zero-ℚ)))

  abstract opaque
    unfolding leq-ℝ' real-dist-located-Metric-Space real-ℚ

    leq-real-dist-Metric-Space :
      (ε : ℚ⁺) →
      leq-ℝ real-dist-located-Metric-Space (real-ℚ⁺ ε) ↔
      neighborhood-Metric-Space M ε x y
    leq-real-dist-Metric-Space ε =
      leq-upper-real-dist-Metric-Space M x y B ε ∘iff
      leq-iff-ℝ' real-dist-located-Metric-Space (real-ℚ⁺ ε)

    is-nonnegative-real-dist-located-Metric-Space :
      is-nonnegative-ℝ real-dist-located-Metric-Space
    is-nonnegative-real-dist-located-Metric-Space =
      leq-leq'-ℝ
        ( zero-ℝ)
        ( real-dist-located-Metric-Space)
        ( leq-zero-upper-real-dist-Metric-Space M x y B)

  nonnegative-real-dist-Metric-Space : nonnegative-ℝ l2
  nonnegative-real-dist-Metric-Space =
    ( real-dist-located-Metric-Space ,
      is-nonnegative-real-dist-located-Metric-Space)
```
