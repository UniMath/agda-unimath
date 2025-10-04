# Located metric spaces

```agda
module metric-spaces.located-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-disjunction
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.elements-at-bounded-distance-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-numbers-from-upper-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) is
{{#concept "located" Disambiguation="metric space" Agda=is-located-Metric-Space}}
if for any `x` and `y` in the metric space, and `δ ε : ℚ⁺` with `δ < ε`, merely
`x` and `y` are [not](foundation.negation.md) in a `δ`-neighborhood
[or](foundation.disjunction.md) `x` and `y` are in an `ε`-neighborhood.

If `x` and `y` are
[at bounded distance](metric-spaces.elements-at-bounded-distance-metric-spaces.md),
then this suffices to define a
[real number](real-numbers.dedekind-real-numbers.md) `d` such that for all
`ε : ℚ⁺`, `d ≤ ε` [if and only if](foundation.logical-equivalences.md) `x` and
`y` are in an `ε`-neighborhood of each other.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  is-located-prop-Metric-Space : Prop (l1 ⊔ l2)
  is-located-prop-Metric-Space =
    Π-Prop
      ( type-Metric-Space M)
      ( λ x →
        Π-Prop
          ( type-Metric-Space M)
          ( λ y →
            Π-Prop
              ( ℚ⁺)
              ( λ δ →
                Π-Prop
                  ( ℚ⁺)
                  ( λ ε →
                    hom-Prop
                      ( le-prop-ℚ⁺ δ ε)
                      ( ¬' (neighborhood-prop-Metric-Space M δ x y) ∨
                        neighborhood-prop-Metric-Space M ε x y)))))

  is-located-Metric-Space : UU (l1 ⊔ l2)
  is-located-Metric-Space = type-Prop is-located-prop-Metric-Space

Located-Metric-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Located-Metric-Space l1 l2 =
  type-subtype (is-located-prop-Metric-Space {l1} {l2})

module _
  {l1 l2 : Level} (X : Located-Metric-Space l1 l2)
  where

  metric-space-Located-Metric-Space : Metric-Space l1 l2
  metric-space-Located-Metric-Space = pr1 X

  type-Located-Metric-Space : UU l1
  type-Located-Metric-Space =
    type-Metric-Space metric-space-Located-Metric-Space

  is-located-metric-space-Located-Metric-Space :
    is-located-Metric-Space metric-space-Located-Metric-Space
  is-located-metric-space-Located-Metric-Space = pr2 X

  set-Located-Metric-Space : Set l1
  set-Located-Metric-Space = set-Metric-Space metric-space-Located-Metric-Space

subset-Located-Metric-Space :
  {l1 l2 : Level} (l3 : Level) (X : Located-Metric-Space l1 l2) →
  UU (l1 ⊔ lsuc l3)
subset-Located-Metric-Space l3 X =
  subset-Metric-Space l3 (metric-space-Located-Metric-Space X)
```

## Properties

### Elements at bounded distance in a located metric space can be assigned a real distance

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
            p⁺ = (p , is-positive-le-zero-ℚ p 0<p)
            p<r = le-left-mediant-ℚ p q p<q
            r<q = le-right-mediant-ℚ p q p<q
            r⁺ =
              ( r ,
                is-positive-le-zero-ℚ r (transitive-le-ℚ zero-ℚ p r p<r 0<p))
          in
            map-disjunction
              ( λ ¬Npxy p∈U →
                let open do-syntax-trunc-Prop empty-Prop
                in do
                  ((ε⁺@(ε , _) , Nεxy) , ε<p) ← p∈U
                  ¬Npxy
                    ( monotonic-neighborhood-Metric-Space M x y ε⁺ p⁺ ε<p Nεxy))
              ( λ Nrxy → intro-exists (r⁺ , Nrxy) r<q)
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

  opaque
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
