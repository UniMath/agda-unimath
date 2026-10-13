# Bounded linear maps on normed real vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module functional-analysis.bounded-linear-maps-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.linear-maps-normed-real-vector-spaces
open import linear-algebra.normed-real-vector-spaces

open import logic.functoriality-existential-quantification

open import metric-spaces.lipschitz-maps-metric-spaces
open import metric-spaces.pointwise-continuous-maps-metric-spaces
open import metric-spaces.pointwise-epsilon-delta-continuous-maps-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import order-theory.large-posets

open import real-numbers.addition-positive-and-negative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

A
{{#concept "bounded linear map" Disambiguation="between normed real vector spaces" WDID=Q2342396 WD="bounded operator" Agda=bounded-linear-map-Normed-ℝ-Vector-Space}}
between [normed real vector spaces](linear-algebra.normed-real-vector-spaces.md)
`V` and `W` is a
[linear map](linear-algebra.linear-maps-normed-real-vector-spaces.md) `f` from
`V` to `W` such that there [exists](foundation.existential-quantification.md) a
[positive rational number](elementary-number-theory.positive-rational-numbers.md)
`M` such that for all `v : V`, `∥f v∥` is
[less than or equal to](real-numbers.inequality-real-numbers.md) `M ∥v∥`.

A linear map `f` is bounded [if and only if](foundation.logical-equivalences.md)
it is a continuous map from the [metric space](metric-spaces.metric-spaces.md)
of `V` to the metric space of `W`, for any of the following forms of continuity:
[Lipschitz](metric-spaces.lipschitz-maps-metric-spaces.md),
[uniform](metric-spaces.uniformly-continuous-maps-metric-spaces.md),
[pointwise](metric-spaces.pointwise-continuous-maps-metric-spaces.md), and
[pointwise ε-δ](metric-spaces.pointwise-epsilon-delta-continuous-maps-metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (W : Normed-ℝ-Vector-Space l1 l3)
  (f : linear-map-Normed-ℝ-Vector-Space V W)
  where

  bounds-norm-prop-linear-map-Normed-ℝ-Vector-Space :
    subtype (l1 ⊔ l2) ℚ⁺
  bounds-norm-prop-linear-map-Normed-ℝ-Vector-Space q =
    Π-Prop
      ( type-Normed-ℝ-Vector-Space V)
      ( λ v →
        leq-prop-ℝ
          ( map-norm-Normed-ℝ-Vector-Space
            ( W)
            ( map-linear-map-Normed-ℝ-Vector-Space V W f v))
          ( real-ℚ⁺ q *ℝ map-norm-Normed-ℝ-Vector-Space V v))

  bounds-norm-linear-map-Normed-ℝ-Vector-Space : ℚ⁺ → UU (l1 ⊔ l2)
  bounds-norm-linear-map-Normed-ℝ-Vector-Space =
    is-in-subtype bounds-norm-prop-linear-map-Normed-ℝ-Vector-Space

  is-bounded-prop-linear-map-Normed-ℝ-Vector-Space : Prop (l1 ⊔ l2)
  is-bounded-prop-linear-map-Normed-ℝ-Vector-Space =
    ∃ ℚ⁺ bounds-norm-prop-linear-map-Normed-ℝ-Vector-Space

  is-bounded-linear-map-Normed-ℝ-Vector-Space : UU (l1 ⊔ l2)
  is-bounded-linear-map-Normed-ℝ-Vector-Space =
    type-Prop is-bounded-prop-linear-map-Normed-ℝ-Vector-Space

bounded-linear-map-Normed-ℝ-Vector-Space :
  {l1 l2 l3 : Level} →
  Normed-ℝ-Vector-Space l1 l2 → Normed-ℝ-Vector-Space l1 l3 →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
bounded-linear-map-Normed-ℝ-Vector-Space V W =
  type-subtype (is-bounded-prop-linear-map-Normed-ℝ-Vector-Space V W)
```

## Properties

### Any pointwise continuous linear map is bounded

```agda
module _
  {l1 l2 l3 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (W : Normed-ℝ-Vector-Space l1 l3)
  (f@(map-f , _ , is-homogeneous-f) : linear-map-Normed-ℝ-Vector-Space V W)
  where

  abstract
    saturated-bound-continuity-linear-map-Normed-ℝ-Vector-Space :
      (δ : ℚ⁺) →
      ( (v : type-Normed-ℝ-Vector-Space V) →
        leq-ℝ (map-norm-Normed-ℝ-Vector-Space V v) (real-ℚ⁺ δ) →
        leq-ℝ (map-norm-Normed-ℝ-Vector-Space W (map-f v)) one-ℝ) →
      (v : type-Normed-ℝ-Vector-Space V) (η : ℚ⁺) →
      leq-ℝ
        ( map-norm-Normed-ℝ-Vector-Space W (map-f v))
        ( ( real-ℚ⁺ (inv-ℚ⁺ δ)) *ℝ
          ( map-norm-Normed-ℝ-Vector-Space V v +ℝ real-ℚ⁺ η))
    saturated-bound-continuity-linear-map-Normed-ℝ-Vector-Space
      δ |v|≤δ⇒|fv|≤1 v η =
      let
        norm = map-norm-Normed-ℝ-Vector-Space
        |v| = norm V v
        |v|⁰⁺ = nonnegative-norm-Normed-ℝ-Vector-Space V v
        _*V_ = mul-Normed-ℝ-Vector-Space V
        _*W_ = mul-Normed-ℝ-Vector-Space W
        |v|+η⁺ = add-nonnegative-positive-ℝ |v|⁰⁺ (positive-real-ℚ⁺ η)
        ⟨|v|+η⟩/δ⁺ = positive-real-ℚ⁺ (inv-ℚ⁺ δ) *ℝ⁺ |v|+η⁺
        ⟨|v|+η⟩/δ = real-ℝ⁺ ⟨|v|+η⟩/δ⁺
        δ/⟨|v|+η⟩ = real-inv-ℝ⁺ ⟨|v|+η⟩/δ⁺
        eq-δ/⟨|v|+η⟩ =
          equational-reasoning
            real-inv-ℝ⁺ ⟨|v|+η⟩/δ⁺
            ＝ real-inv-ℝ⁺ (positive-real-ℚ⁺ (inv-ℚ⁺ δ)) *ℝ real-inv-ℝ⁺ |v|+η⁺
              by ap real-ℝ⁺ (distributive-inv-mul-ℝ⁺ _ _)
            ＝ real-ℚ⁺ (inv-ℚ⁺ (inv-ℚ⁺ δ)) *ℝ real-inv-ℝ⁺ |v|+η⁺
              by ap-mul-ℝ (ap real-ℝ⁺ (inv-positive-real-ℚ⁺ (inv-ℚ⁺ δ))) refl
            ＝ real-ℚ⁺ δ *ℝ real-inv-ℝ⁺ |v|+η⁺
              by ap-mul-ℝ (ap real-ℚ⁺ (inv-inv-ℚ⁺ δ)) refl
            ＝ raise-real-ℚ⁺ l1 δ *ℝ real-inv-ℝ⁺ |v|+η⁺
              by inv (eq-mul-left-raise-ℝ _ _)
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
          norm W (map-f v)
          ≤ norm W (map-f (⟨|v|+η⟩/δ *V (δ/⟨|v|+η⟩ *V v)))
            by
              leq-eq-ℝ
                ( ap
                  ( norm W ∘ map-f)
                  ( inv
                    ( is-section-map-inv-equiv
                      ( equiv-mul-positive-Normed-ℝ-Vector-Space V ⟨|v|+η⟩/δ⁺)
                      ( v))))
          ≤ norm W (⟨|v|+η⟩/δ *W map-f (δ/⟨|v|+η⟩ *V v))
            by leq-eq-ℝ (ap (norm W) (is-homogeneous-f ⟨|v|+η⟩/δ _))
          ≤ ⟨|v|+η⟩/δ *ℝ norm W (map-f (δ/⟨|v|+η⟩ *V v))
            by leq-eq-ℝ (norm-mul-positive-Normed-ℝ-Vector-Space W ⟨|v|+η⟩/δ⁺ _)
          ≤ ⟨|v|+η⟩/δ *ℝ one-ℝ
            by
              preserves-leq-left-mul-ℝ⁺
                ( ⟨|v|+η⟩/δ⁺)
                ( |v|≤δ⇒|fv|≤1
                  ( δ/⟨|v|+η⟩ *V v)
                  ( chain-of-inequalities
                    norm V (δ/⟨|v|+η⟩ *V v)
                    ≤ norm V ((raise-real-ℚ⁺ l1 δ *ℝ real-inv-ℝ⁺ |v|+η⁺) *V v)
                      by leq-eq-ℝ (ap (λ c → norm V (c *V v)) eq-δ/⟨|v|+η⟩)
                    ≤ norm V (raise-real-ℚ⁺ l1 δ *V (real-inv-ℝ⁺ |v|+η⁺ *V v))
                      by
                        leq-eq-ℝ
                          ( ap
                            ( norm V)
                            ( associative-mul-Normed-ℝ-Vector-Space V _ _ _))
                    ≤ raise-real-ℚ⁺ l1 δ *ℝ norm V (real-inv-ℝ⁺ |v|+η⁺ *V v)
                      by
                        leq-eq-ℝ
                          ( norm-mul-positive-Normed-ℝ-Vector-Space V
                            ( positive-raise-real-ℚ⁺ l1 δ)
                            ( _))
                    ≤ raise-real-ℚ⁺ l1 δ *ℝ one-ℝ
                      by
                        preserves-leq-left-mul-ℝ⁺
                          ( positive-raise-real-ℚ⁺ l1 δ)
                          ( leq-one-norm-mul-inv-norm-plus-positive-rational-Normed-ℝ-Vector-Space
                            ( V)
                            ( v)
                            ( η))
                    ≤ raise-real-ℚ⁺ l1 δ
                      by leq-eq-ℝ (right-unit-law-mul-ℝ _)
                    ≤ real-ℚ⁺ δ
                      by leq-sim-ℝ (sim-raise-ℝ' l1 _)))
          ≤ ⟨|v|+η⟩/δ
            by leq-eq-ℝ (right-unit-law-mul-ℝ ⟨|v|+η⟩/δ)

    is-bounded-is-pointwise-ε-δ-continuous-map-linear-map-Normed-ℝ-Vector-Space :
      is-pointwise-ε-δ-continuous-map-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( metric-space-Normed-ℝ-Vector-Space W)
        ( map-linear-map-Normed-ℝ-Vector-Space V W f) →
      is-bounded-linear-map-Normed-ℝ-Vector-Space V W f
    is-bounded-is-pointwise-ε-δ-continuous-map-linear-map-Normed-ℝ-Vector-Space
      H =
      elim-exists
        ( is-bounded-prop-linear-map-Normed-ℝ-Vector-Space V W f)
        ( λ δ dv0≤δ⇒dfvf0≤1 →
          intro-exists
            ( inv-ℚ⁺ δ)
            ( λ v →
              saturated-leq-left-mul-ℝ⁰⁺
                ( nonnegative-norm-Normed-ℝ-Vector-Space W (map-f v))
                ( nonnegative-real-ℚ⁺ (inv-ℚ⁺ δ))
                ( nonnegative-norm-Normed-ℝ-Vector-Space V v)
                ( saturated-bound-continuity-linear-map-Normed-ℝ-Vector-Space
                    ( δ)
                    ( λ v' →
                      binary-tr
                        ( λ x y → leq-ℝ x (real-ℚ⁺ δ) → leq-ℝ y one-ℝ)
                        ( left-zero-law-dist-Normed-ℝ-Vector-Space V v')
                        ( ( ap-binary
                            ( dist-Normed-ℝ-Vector-Space W)
                            ( is-zero-map-zero-linear-map-Normed-ℝ-Vector-Space
                              ( V)
                              ( W)
                              ( f))
                            ( refl)) ∙
                          ( left-zero-law-dist-Normed-ℝ-Vector-Space W
                            ( map-f v')))
                        ( dv0≤δ⇒dfvf0≤1 v'))
                    ( v))))
        ( H (zero-Normed-ℝ-Vector-Space V) one-ℚ⁺)
```

### Any bounded linear map is Lipschitz continuous

```agda
module _
  {l1 l2 l3 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (W : Normed-ℝ-Vector-Space l1 l3)
  (f@(map-f , _ , _) : linear-map-Normed-ℝ-Vector-Space V W)
  where

  abstract
    is-lipschitz-map-is-bounded-linear-map-Normed-ℝ-Vector-Space :
      is-bounded-linear-map-Normed-ℝ-Vector-Space V W f →
      is-lipschitz-map-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( metric-space-Normed-ℝ-Vector-Space W)
        ( map-linear-map-Normed-ℝ-Vector-Space V W f)
    is-lipschitz-map-is-bounded-linear-map-Normed-ℝ-Vector-Space =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        map-tot-exists
          ( λ M |fv|≤M|v| d x y dxy≤d →
            chain-of-inequalities
              dist-Normed-ℝ-Vector-Space W (map-f x) (map-f y)
              ≤ map-norm-Normed-ℝ-Vector-Space W
                  ( map-f (diff-Normed-ℝ-Vector-Space V x y))
                by
                  leq-eq-ℝ
                    ( ap
                      ( map-norm-Normed-ℝ-Vector-Space W)
                      ( inv (map-diff-linear-map-Normed-ℝ-Vector-Space V W f)))
              ≤ real-ℚ⁺ M *ℝ dist-Normed-ℝ-Vector-Space V x y
                by |fv|≤M|v| (diff-Normed-ℝ-Vector-Space V x y)
              ≤ real-ℚ⁺ M *ℝ real-ℚ⁺ d
                by preserves-leq-left-mul-ℝ⁺ (positive-real-ℚ⁺ M) dxy≤d
              ≤ real-ℚ⁺ (M *ℚ⁺ d)
                by leq-eq-ℝ (mul-real-ℚ _ _))

    is-uniformly-continuous-map-is-bounded-linear-map-Normed-ℝ-Vector-Space :
      is-bounded-linear-map-Normed-ℝ-Vector-Space V W f →
      is-uniformly-continuous-map-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( metric-space-Normed-ℝ-Vector-Space W)
        ( map-linear-map-Normed-ℝ-Vector-Space V W f)
    is-uniformly-continuous-map-is-bounded-linear-map-Normed-ℝ-Vector-Space =
      ( is-uniformly-continuous-map-is-lipschitz-map-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( metric-space-Normed-ℝ-Vector-Space W)
        ( map-linear-map-Normed-ℝ-Vector-Space V W f)) ∘
      ( is-lipschitz-map-is-bounded-linear-map-Normed-ℝ-Vector-Space)

    is-pointwise-continuous-map-is-bounded-linear-map-Normed-ℝ-Vector-Space :
      is-bounded-linear-map-Normed-ℝ-Vector-Space V W f →
      is-pointwise-continuous-map-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( metric-space-Normed-ℝ-Vector-Space W)
        ( map-linear-map-Normed-ℝ-Vector-Space V W f)
    is-pointwise-continuous-map-is-bounded-linear-map-Normed-ℝ-Vector-Space =
      ( is-pointwise-continuous-map-is-uniformly-continuous-map-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( metric-space-Normed-ℝ-Vector-Space W)
        ( map-linear-map-Normed-ℝ-Vector-Space V W f)) ∘
      ( is-uniformly-continuous-map-is-bounded-linear-map-Normed-ℝ-Vector-Space)

    is-pointwise-ε-δ-continuous-map-is-bounded-linear-map-Normed-ℝ-Vector-Space :
      is-bounded-linear-map-Normed-ℝ-Vector-Space V W f →
      is-pointwise-ε-δ-continuous-map-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( metric-space-Normed-ℝ-Vector-Space W)
        ( map-linear-map-Normed-ℝ-Vector-Space V W f)
    is-pointwise-ε-δ-continuous-map-is-bounded-linear-map-Normed-ℝ-Vector-Space =
      ( is-pointwise-ε-δ-continuous-map-is-pointwise-continuous-map-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( metric-space-Normed-ℝ-Vector-Space W)
        ( map-linear-map-Normed-ℝ-Vector-Space V W f)) ∘
      ( is-pointwise-continuous-map-is-bounded-linear-map-Normed-ℝ-Vector-Space)
```

### Boundedness is equivalent to pointwise ε-δ continuity for linear maps

```agda
module _
  {l1 l2 l3 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (W : Normed-ℝ-Vector-Space l1 l3)
  (f : linear-map-Normed-ℝ-Vector-Space V W)
  where

  iff-is-pointwise-ε-δ-continuous-map-is-bounded-linear-map-Normed-ℝ-Vector-Space :
    is-bounded-linear-map-Normed-ℝ-Vector-Space V W f ↔
    is-pointwise-ε-δ-continuous-map-Metric-Space
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( metric-space-Normed-ℝ-Vector-Space W)
      ( map-linear-map-Normed-ℝ-Vector-Space V W f)
  iff-is-pointwise-ε-δ-continuous-map-is-bounded-linear-map-Normed-ℝ-Vector-Space =
    ( is-pointwise-ε-δ-continuous-map-is-bounded-linear-map-Normed-ℝ-Vector-Space
        ( V)
        ( W)
        ( f) ,
      is-bounded-is-pointwise-ε-δ-continuous-map-linear-map-Normed-ℝ-Vector-Space
        ( V)
        ( W)
        ( f))
```

## External links

- [Bounded operator](https://en.wikipedia.org/wiki/Bounded_operator) on
  Wikipedia
