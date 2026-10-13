# Nontrivial normed real vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.nontrivial-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels-unit-type
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.apartness-normed-real-vector-spaces
open import linear-algebra.nonzero-vectors-normed-real-vector-spaces
open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.trivial-real-vector-spaces
open import linear-algebra.unit-vectors-normed-real-vector-spaces

open import metric-spaces.accumulation-points-subsets-located-metric-spaces
open import metric-spaces.perfect-metric-spaces

open import order-theory.large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.zero-real-numbers
```

</details>

## Idea

A [normed real vector space](linear-algebra.normed-real-vector-spaces.md) `V` is
{{#concept "nontrivial" Disambiguation="normed real vector space" Agda=is-nontrivial-Normed-ℝ-Vector-Space}}
if there [exists](foundation.existential-quantification.md) a
[nonzero vector](linear-algebra.nonzero-vectors-normed-real-vector-spaces.md) in
`V`.

A normed real vector space is nontrivial
[if and only if](foundation.logical-equivalences.md) it is
[perfect](metric-spaces.perfect-metric-spaces.md) as a
[located metric space](metric-spaces.located-metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  is-nontrivial-prop-Normed-ℝ-Vector-Space : Prop (l1 ⊔ l2)
  is-nontrivial-prop-Normed-ℝ-Vector-Space =
    ∃ ( type-Normed-ℝ-Vector-Space V)
      ( is-nonzero-prop-Normed-ℝ-Vector-Space V)

  is-nontrivial-Normed-ℝ-Vector-Space : UU (l1 ⊔ l2)
  is-nontrivial-Normed-ℝ-Vector-Space =
    type-Prop is-nontrivial-prop-Normed-ℝ-Vector-Space
```

## Properties

### A normed real vector space is not nontrivial if and only if it is trivial

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where abstract

  is-trivial-is-not-nontrivial-Normed-ℝ-Vector-Space :
    ¬ is-nontrivial-Normed-ℝ-Vector-Space V →
    is-trivial-ℝ-Vector-Space (vector-space-Normed-ℝ-Vector-Space V)
  is-trivial-is-not-nontrivial-Normed-ℝ-Vector-Space ¬|v|>0 =
    ( zero-Normed-ℝ-Vector-Space V ,
      λ w →
        inv
          ( is-zero-is-not-nonzero-Normed-ℝ-Vector-Space V w
            ( map-neg (intro-exists w) ¬|v|>0)))

  is-not-nontrivial-is-trivial-Normed-ℝ-Vector-Space :
    is-trivial-ℝ-Vector-Space (vector-space-Normed-ℝ-Vector-Space V) →
    ¬ is-nontrivial-Normed-ℝ-Vector-Space V
  is-not-nontrivial-is-trivial-Normed-ℝ-Vector-Space is-contr-V =
    elim-exists
      ( empty-Prop)
      ( λ v →
        is-not-positive-is-zero-ℝ
          ( map-norm-Normed-ℝ-Vector-Space V v)
          ( tr
            ( is-zero-ℝ ∘ map-norm-Normed-ℝ-Vector-Space V)
            ( eq-is-contr is-contr-V)
            ( is-zero-map-norm-zero-Normed-ℝ-Vector-Space V)))
```

### If a normed real vector space is nontrivial, it contains a unit vector

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where abstract

  contains-unit-is-nontrivial-Normed-ℝ-Vector-Space :
    is-nontrivial-Normed-ℝ-Vector-Space V →
    is-inhabited (unit-Normed-ℝ-Vector-Space V)
  contains-unit-is-nontrivial-Normed-ℝ-Vector-Space =
    map-trunc-Prop (unit-nonzero-vector-Normed-ℝ-Vector-Space V)
```

### If a normed real vector space is nontrivial, it has vectors of every nonnegative length

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (d : ℝ⁰⁺ l1)
  where abstract

  exists-vector-with-norm-is-nontrivial-Normed-ℝ-Vector-Space :
    is-nontrivial-Normed-ℝ-Vector-Space V →
    exists
      ( type-Normed-ℝ-Vector-Space V)
      ( has-norm-prop-Normed-ℝ-Vector-Space V d)
  exists-vector-with-norm-is-nontrivial-Normed-ℝ-Vector-Space =
    map-trunc-Prop
      ( λ v →
        ( normalized-to-norm-nonzero-vector-Normed-ℝ-Vector-Space V d v ,
          has-norm-normalized-to-norm-nonzero-vector-Normed-ℝ-Vector-Space V
            ( d)
            ( v)))
```

### If a normed real vector space is nontrivial, it is perfect

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where abstract

  open inequality-reasoning-Large-Poset ℝ-Large-Poset

  is-perfect-is-nontrivial-Normed-ℝ-Vector-Space :
    is-nontrivial-Normed-ℝ-Vector-Space V →
    is-perfect-Located-Metric-Space
      ( located-metric-space-Normed-ℝ-Vector-Space V)
  is-perfect-is-nontrivial-Normed-ℝ-Vector-Space NT v =
    map-trunc-Prop
      ( λ uŵ@(ŵ , |ŵ|=1) →
        let
          _+V_ = add-Normed-ℝ-Vector-Space V
          _*V_ = mul-Normed-ℝ-Vector-Space V
          w ε = v +V (raise-real-ℚ⁺ l1 ε *V ŵ)
          |wε-v|=ε ε =
            ( dist-add-Normed-ℝ-Vector-Space V _ _) ∙
            ( map-norm-mul-positive-unit-Normed-ℝ-Vector-Space V
              ( positive-raise-real-ℚ⁺ l1 ε)
              ( uŵ))
          |wε-v|≤ε ε =
            transitive-leq-ℝ _ _ _
              ( leq-sim-ℝ (sim-raise-ℝ' l1 (real-ℚ⁺ ε)))
              ( leq-eq-ℝ (|wε-v|=ε ε))
          is-cauchy-w :
            (δ ε : ℚ⁺) →
            neighborhood-Normed-ℝ-Metric-Space V (δ +ℚ⁺ ε) (w δ) (w ε)
          is-cauchy-w δ ε =
            chain-of-inequalities
              dist-Normed-ℝ-Vector-Space V (w δ) (w ε)
              ≤ dist-Normed-ℝ-Vector-Space V (w δ) v +ℝ
                dist-Normed-ℝ-Vector-Space V v (w ε)
                by triangular-dist-Normed-ℝ-Vector-Space V (w δ) v (w ε)
              ≤ dist-Normed-ℝ-Vector-Space V (w δ) v +ℝ
                dist-Normed-ℝ-Vector-Space V (w ε) v
                by
                  leq-eq-ℝ
                    ( ap-add-ℝ
                      ( refl)
                      ( symmetric-dist-Normed-ℝ-Vector-Space V _ _))
              ≤ real-ℚ⁺ δ +ℝ real-ℚ⁺ ε
                by preserves-leq-add-ℝ (|wε-v|≤ε δ) (|wε-v|≤ε ε)
              ≤ real-ℚ⁺ (δ +ℚ⁺ ε)
                by leq-eq-ℝ (add-real-ℚ _ _)
          apart-w ε =
            apart-located-metric-space-apart-Normed-ℝ-Vector-Space
              ( V)
              ( w ε)
              ( v)
              ( inv-tr
                ( is-positive-ℝ)
                ( |wε-v|=ε ε)
                ( is-positive-real-ℝ⁺ (positive-raise-real-ℚ⁺ l1 ε)))
          is-limit-w-v δ ε =
            transitive-leq-ℝ _ _ _
              ( preserves-leq-real-ℚ
                ( leq-right-add-rational-ℚ⁺ (rational-ℚ⁺ δ) ε))
              ( |wε-v|≤ε δ)
        in
          ( ( ( λ ε → (w ε , raise-star)) ,
              is-cauchy-w) ,
            apart-w ,
            is-limit-w-v))
      ( contains-unit-is-nontrivial-Normed-ℝ-Vector-Space V NT)
```

### If a normed real vector space is perfect, it is nontrivial

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where abstract

  is-nontrivial-is-perfect-Normed-ℝ-Vector-Space :
    is-perfect-Located-Metric-Space
      ( located-metric-space-Normed-ℝ-Vector-Space V) →
    is-nontrivial-Normed-ℝ-Vector-Space V
  is-nontrivial-is-perfect-Normed-ℝ-Vector-Space P =
    let open do-syntax-trunc-Prop (is-nontrivial-prop-Normed-ℝ-Vector-Space V)
    in do
      ((approx-0 , _) , apart-approx-0 , _) ← P (zero-Normed-ℝ-Vector-Space V)
      let (v , _) = approx-0 one-ℚ⁺
      intro-exists
        ( v)
        ( is-nonzero-is-apart-zero-Normed-ℝ-Vector-Space V
          ( v)
          ( apart-apart-located-metric-space-Normed-ℝ-Vector-Space
            ( V)
            ( v)
            ( zero-Normed-ℝ-Vector-Space V)
            ( apart-approx-0 one-ℚ⁺)))
```
