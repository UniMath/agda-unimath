# Differentiable maps from proper closed intervals on ℝ to normed real vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import functional-analysis.modulated-uniformly-continuous-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces
open import functional-analysis.uniformly-continuous-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces

open import group-theory.abelian-groups

open import linear-algebra.normed-real-vector-spaces

open import lists.sequences

open import metric-spaces.limits-of-sequences-metric-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.accumulation-points-subsets-real-numbers
open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.apartness-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-nonzero-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.nonzero-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

Given a map `f` from a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
`[a, b]` of [real numbers](real-numbers.dedekind-real-numbers.md) to a
[normed real vector space](linear-algebra.normed-real-vector-spaces.md) `V`, `g`
is a
{{#concept "derivative" Disambiguation="of map from a proper closed interval in ℝ to a normed real vector space" WD="derivative" WDID=Q29175 Agda=is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space}}
of `f` if there [exists](foundation.existential-quantification.md) a modulus
function `μ` such that for `ε : ℚ⁺` and any `x` and `y` in `[a, b]` within a
`μ(ε)`-[neighborhood](real-numbers.metric-space-of-real-numbers.md) of each
other, we have $$∥f(y) - f(x) - (y - x)g(x)∥ ≤ ε|y - x|.$$

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f g : type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  where

  is-modulus-of-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    subtype (lsuc l1) (ℚ⁺ → ℚ⁺)
  is-modulus-of-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
    μ =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( type-proper-closed-interval-ℝ l1 [a,b])
          ( λ (x , x∈[a,b]) →
            Π-Prop
              ( type-proper-closed-interval-ℝ l1 [a,b])
              ( λ (y , y∈[a,b]) →
                hom-Prop
                  ( neighborhood-prop-ℝ l1 (μ ε) x y)
                  ( leq-prop-ℝ
                    ( dist-Normed-ℝ-Vector-Space V
                      ( diff-Normed-ℝ-Vector-Space V
                        ( f (y , y∈[a,b]))
                        ( f (x , x∈[a,b])))
                      ( mul-Normed-ℝ-Vector-Space V (y -ℝ x) (g (x , x∈[a,b]))))
                    ( real-ℚ⁺ ε *ℝ dist-ℝ y x)))))

  is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    (ℚ⁺ → ℚ⁺) → UU (lsuc l1)
  is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    is-in-subtype
      ( is-modulus-of-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    Prop (lsuc l1)
  is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    is-inhabited-subtype-Prop
      ( is-modulus-of-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    UU (lsuc l1)
  is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    type-Prop
      ( is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  where

  is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    (type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V) →
    UU (lsuc l1 ⊔ l2)
  is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space f =
    Σ ( type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
      ( is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( f))

  differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    UU (lsuc l1 ⊔ l2)
  differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    Σ ( type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
      ( is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space →
    type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V
  map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space = pr1

  map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space →
    type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V
  map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    pr1 ∘ pr2

  is-derivative-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    (f : differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space) →
    is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( f))
      ( map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( f))
  is-derivative-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    pr2 ∘ pr2
```

## Properties

### Proving the derivative of a map from a modulus

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f g : type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  where abstract

  is-derivative-modulus-of-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    ( (ε : ℚ⁺) →
      Σ ( ℚ⁺)
        ( λ δ →
          (x y : type-proper-closed-interval-ℝ l1 [a,b]) →
          neighborhood-ℝ l1 δ (pr1 x) (pr1 y) →
          leq-ℝ
            ( dist-Normed-ℝ-Vector-Space V
              ( diff-Normed-ℝ-Vector-Space V (f y) (f x))
              ( mul-Normed-ℝ-Vector-Space V (pr1 y -ℝ pr1 x) (g x)))
            ( real-ℚ⁺ ε *ℝ dist-ℝ (pr1 y) (pr1 x)))) →
    is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f)
      ( g)
  is-derivative-modulus-of-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
    M =
    intro-exists (pr1 ∘ M) (pr2 ∘ M)
```

### If `g` is a derivative of `f`, and `aₙ` is a sequence accumulating to `x`, and the limit exists, then `g x` is equal to the limit of `(f aₙ - f x)/(aₙ - x)` as `n → ∞`

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  ((x , x∈[a,b]) : type-proper-closed-interval-ℝ l1 [a,b])
  (y@(sequence-y , _) :
    sequence-accumulating-to-point-subset-ℝ
      ( subtype-proper-closed-interval-ℝ l1 [a,b])
      ( x))
  where

  sequence-derivative-accumulating-to-point-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    sequence (type-Normed-ℝ-Vector-Space V)
  sequence-derivative-accumulating-to-point-proper-closed-interval-real-Normed-ℝ-Vector-Space
    n =
    mul-Normed-ℝ-Vector-Space
      ( V)
      ( real-inv-nonzero-ℝ
        ( nonzero-diff-apart-ℝ
          ( real-sequence-accumulating-to-point-subset-ℝ
            ( subtype-proper-closed-interval-ℝ l1 [a,b])
            ( x)
            ( y)
            ( n))
          ( x)
          ( apart-sequence-accumulating-to-point-subset-ℝ
            ( subtype-proper-closed-interval-ℝ l1 [a,b])
            ( x)
            ( y)
            ( n))))
      ( diff-Normed-ℝ-Vector-Space V
        ( f (sequence-y n))
        ( f (x , x∈[a,b])))

module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f g : type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  (x@(xℝ , xℝ∈[a,b]) : type-proper-closed-interval-ℝ l1 [a,b])
  (y@(seq-y , apart-y , lim-y→x) :
    sequence-accumulating-to-point-subset-ℝ
      ( subtype-proper-closed-interval-ℝ l1 [a,b])
      ( xℝ))
  where abstract

  is-limit-sequence-derivative-accumulating-to-point-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f)
      ( g) →
    is-limit-sequence-Metric-Space
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( sequence-derivative-accumulating-to-point-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( f)
        ( x)
        ( y))
      ( g x)
  is-limit-sequence-derivative-accumulating-to-point-proper-closed-interval-real-Normed-ℝ-Vector-Space
    is-derivative-f-g =
    let
      open
        do-syntax-trunc-Prop
          ( is-limit-prop-sequence-Metric-Space
            ( metric-space-Normed-ℝ-Vector-Space V)
            ( sequence-derivative-accumulating-to-point-proper-closed-interval-real-Normed-ℝ-Vector-Space
              ( V)
              ( [a,b])
              ( f)
              ( x)
              ( y))
            ( g x))
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
      seq-deriv =
        sequence-derivative-accumulating-to-point-proper-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b])
          ( f)
          ( x)
          ( y)
      nonzero-diff n =
        nonzero-diff-apart-ℝ
          ( real-sequence-accumulating-to-point-subset-ℝ
            ( subtype-proper-closed-interval-ℝ l1 [a,b])
            ( xℝ)
            ( y)
            ( n))
          ( xℝ)
          ( apart-sequence-accumulating-to-point-subset-ℝ
            ( subtype-proper-closed-interval-ℝ l1 [a,b])
            ( xℝ)
            ( y)
            ( n))
      real-nonzero-diff n = real-nonzero-ℝ (nonzero-diff n)
      dist-V = dist-Normed-ℝ-Vector-Space V
      _*V_ = mul-Normed-ℝ-Vector-Space V
      _-V_ = diff-Normed-ℝ-Vector-Space V
    in do
      (μ , is-mod-μ) ←
        is-limit-sequence-accumulating-to-point-subset-ℝ
          ( subtype-proper-closed-interval-ℝ l1 [a,b])
          ( xℝ)
          ( y)
      (ν , is-mod-ν) ← is-derivative-f-g
      intro-exists
        ( μ ∘ ν)
        ( λ ε n N≤n →
          chain-of-inequalities
            dist-V (seq-deriv n) (g x)
            ≤ dist-V
                ( seq-deriv n)
                ( raise-one-ℝ l1 *V g x)
              by
                leq-eq-ℝ
                  ( ap-binary
                    ( dist-V)
                    ( refl)
                    ( inv (left-unit-law-mul-Normed-ℝ-Vector-Space V (g x))))
            ≤ dist-V
                ( real-inv-nonzero-ℝ (nonzero-diff n) *V (f (seq-y n) -V f x))
                ( ( real-inv-nonzero-ℝ (nonzero-diff n) *ℝ
                    real-nonzero-diff n) *V
                  ( g x))
              by
                leq-eq-ℝ
                  ( ap-binary
                    ( dist-V)
                    ( refl)
                    ( ap-binary
                      ( _*V_)
                      ( inv
                        ( eq-left-inverse-law-mul-nonzero-ℝ (nonzero-diff n)))
                      ( refl)))
            ≤ dist-V
                ( real-inv-nonzero-ℝ (nonzero-diff n) *V (f (seq-y n) -V f x))
                ( ( real-inv-nonzero-ℝ (nonzero-diff n)) *V
                  ( real-nonzero-diff n *V g x))
              by
                leq-eq-ℝ
                  ( ap-binary
                    ( dist-V)
                    ( refl)
                    ( associative-mul-Normed-ℝ-Vector-Space V _ _ _))
            ≤ ( abs-ℝ (real-inv-nonzero-ℝ (nonzero-diff n))) *ℝ
              ( dist-V (f (seq-y n) -V f x) (real-nonzero-diff n *V g x))
              by
                leq-eq-ℝ
                  ( inv
                    ( left-distributive-abs-mul-dist-Normed-ℝ-Vector-Space V
                      ( _)
                      ( _)
                      ( _)))
            ≤ ( abs-ℝ (real-inv-nonzero-ℝ (nonzero-diff n))) *ℝ
              ( real-ℚ⁺ ε *ℝ dist-ℝ (pr1 (seq-y n)) xℝ)
              by
                preserves-leq-left-mul-ℝ⁰⁺
                  ( nonnegative-abs-ℝ _)
                  ( is-mod-ν
                    ( ε)
                    ( x)
                    ( seq-y n)
                    ( is-symmetric-neighborhood-ℝ
                      ( ν ε)
                      ( pr1 (seq-y n))
                      ( xℝ)
                      ( is-mod-μ (ν ε) n N≤n)))
            ≤ ( real-ℚ⁺ ε) *ℝ
              ( ( abs-ℝ (real-inv-nonzero-ℝ (nonzero-diff n))) *ℝ
                ( dist-ℝ (pr1 (seq-y n)) xℝ))
              by leq-eq-ℝ (left-swap-mul-ℝ _ _ _)
            ≤ ( real-ℚ⁺ ε) *ℝ
              ( abs-ℝ
                ( real-inv-nonzero-ℝ (nonzero-diff n) *ℝ real-nonzero-diff n))
              by leq-eq-ℝ (ap-mul-ℝ refl (inv (abs-mul-ℝ _ _)))
            ≤ real-ℚ⁺ ε *ℝ abs-ℝ one-ℝ
              by
                leq-sim-ℝ
                  ( preserves-sim-left-mul-ℝ (real-ℚ⁺ ε) _ _
                    ( preserves-sim-abs-ℝ
                      ( left-inverse-law-mul-nonzero-ℝ (nonzero-diff n))))
            ≤ real-ℚ⁺ ε *ℝ one-ℝ
              by leq-eq-ℝ (ap-mul-ℝ refl (abs-real-ℝ⁰⁺ one-ℝ⁰⁺))
            ≤ real-ℚ⁺ ε
              by leq-eq-ℝ (right-unit-law-mul-ℝ _))
```

### Any two derivatives of a map are homotopic

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f g h :
    type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  where abstract

  htpy-is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f)
      ( g) →
    is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f)
      ( h) →
    g ~ h
  htpy-is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
    Dg Dh x@(xℝ , x∈[a,b]) =
    rec-trunc-Prop
      ( Id-Prop (set-Normed-ℝ-Vector-Space V) (g x) (h x))
      ( λ y →
        eq-limit-sequence-Metric-Space
          ( metric-space-Normed-ℝ-Vector-Space V)
          ( sequence-derivative-accumulating-to-point-proper-closed-interval-real-Normed-ℝ-Vector-Space
            ( V)
            ( [a,b])
            ( f)
            ( x)
            ( y))
          ( g x)
          ( h x)
          ( is-limit-sequence-derivative-accumulating-to-point-proper-closed-interval-real-Normed-ℝ-Vector-Space
            ( V)
            ( [a,b])
            ( f)
            ( g)
            ( x)
            ( y)
            ( Dg))
          ( is-limit-sequence-derivative-accumulating-to-point-proper-closed-interval-real-Normed-ℝ-Vector-Space
            ( V)
            ( [a,b])
            ( f)
            ( h)
            ( x)
            ( y)
            ( Dh)))
      ( is-sequential-accumulation-point-is-accumulation-point-subset-ℝ
        ( subtype-proper-closed-interval-ℝ l1 [a,b])
        ( xℝ)
        ( is-accumulation-point-is-in-proper-closed-interval-ℝ
          ( [a,b])
          ( xℝ)
          ( x∈[a,b])))
```

### Being differentiable is a proposition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  where

  abstract
    all-elements-equal-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
      all-elements-equal
        ( is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b])
          ( f))
    all-elements-equal-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      (g , Dg) (h , Dh) =
      eq-type-subtype
        ( is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b])
          ( f))
        ( eq-htpy
          ( htpy-is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
            ( V)
            ( [a,b])
            ( f)
            ( g)
            ( h)
            ( Dg)
            ( Dh)))

    is-prop-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
      is-prop
        ( is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b])
          ( f))
    is-prop-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
      is-prop-all-elements-equal
        ( all-elements-equal-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    Prop (lsuc l1 ⊔ l2)
  is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    ( is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( f) ,
      is-prop-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
```

### A derivative of a map from a proper closed interval to a normed real vector space is uniformly continuous

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f f' : type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  (δf : ℚ⁺ → ℚ⁺)
  (is-mod-derivative-f-f'-δf :
    is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f)
      ( f')
      ( δf))
  where abstract

  apart-modulus-is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    ℚ⁺ → ℚ⁺
  apart-modulus-is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    δf ∘ modulus-le-double-le-ℚ⁺

  is-apart-modulus-is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    (ε : ℚ⁺) (x y : type-proper-closed-interval-ℝ l1 [a,b]) →
    apart-ℝ (pr1 x) (pr1 y) →
    neighborhood-ℝ _
      ( apart-modulus-is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( ε))
      ( pr1 x)
      ( pr1 y) →
    neighborhood-Normed-ℝ-Vector-Space V ε (f' x) (f' y)
  is-apart-modulus-is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
    ε x@(xℝ , _) y@(yℝ , _) x#y Nμεxy =
    let
      (ε' , ε'+ε'<ε) = bound-double-le-ℚ⁺ ε
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
      dist-V = dist-Normed-ℝ-Vector-Space V
      _*V_ = mul-Normed-ℝ-Vector-Space V
      _-V_ = diff-Normed-ℝ-Vector-Space V
      neg-V = neg-Normed-ℝ-Vector-Space V
    in
      reflects-leq-left-mul-ℝ⁺
        ( dist-ℝ xℝ yℝ , is-positive-dist-apart-ℝ x#y)
        ( _)
        ( _)
        ( chain-of-inequalities
          dist-ℝ xℝ yℝ *ℝ dist-V (f' x) (f' y)
          ≤ dist-V ((xℝ -ℝ yℝ) *V f' x) ((xℝ -ℝ yℝ) *V f' y)
            by
              leq-eq-ℝ
                ( left-distributive-abs-mul-dist-Normed-ℝ-Vector-Space V
                  ( xℝ -ℝ yℝ)
                  ( f' x)
                  ( f' y))
          ≤ dist-V ((xℝ -ℝ yℝ) *V f' x) (f x -V f y) +ℝ
            dist-V (f x -V f y) ((xℝ -ℝ yℝ) *V f' y)
            by triangular-dist-Normed-ℝ-Vector-Space V _ _ _
          ≤ dist-V (f x -V f y) ((xℝ -ℝ yℝ) *V f' x) +ℝ
            dist-V (f x -V f y) ((xℝ -ℝ yℝ) *V f' y)
            by
              leq-eq-ℝ
                ( ap-add-ℝ (symmetric-dist-Normed-ℝ-Vector-Space V _ _) refl)
          ≤ dist-V (neg-V (f x -V f y)) (neg-V ((xℝ -ℝ yℝ) *V f' x)) +ℝ
            dist-V (f x -V f y) ((xℝ -ℝ yℝ) *V f' y)
            by
              leq-eq-ℝ
                ( ap-add-ℝ (inv (dist-neg-Normed-ℝ-Vector-Space V _ _)) refl)
          ≤ dist-V (f y -V f x) (neg-ℝ (xℝ -ℝ yℝ) *V f' x) +ℝ
            dist-V (f x -V f y) ((xℝ -ℝ yℝ) *V f' y)
            by
              leq-eq-ℝ
                ( ap-add-ℝ
                  ( ap-binary
                    ( dist-V)
                    ( neg-right-subtraction-Ab
                      ( ab-Normed-ℝ-Vector-Space V)
                      ( f x)
                      ( f y))
                    ( inv (left-negative-law-mul-Normed-ℝ-Vector-Space V _ _)))
                  ( refl))
          ≤ dist-V (f y -V f x) ((yℝ -ℝ xℝ) *V f' x) +ℝ
            dist-V (f x -V f y) ((xℝ -ℝ yℝ) *V f' y)
            by
              leq-eq-ℝ
                ( ap-add-ℝ
                  ( ap-binary
                    ( dist-V)
                    ( refl)
                    ( ap-binary _*V_ (distributive-neg-diff-ℝ xℝ yℝ) refl))
                  ( refl))
          ≤ ( real-ℚ⁺ ε' *ℝ dist-ℝ yℝ xℝ) +ℝ
            ( real-ℚ⁺ ε' *ℝ dist-ℝ xℝ yℝ)
            by
              preserves-leq-add-ℝ
                ( is-mod-derivative-f-f'-δf ε' x y Nμεxy)
                ( is-mod-derivative-f-f'-δf ε' y x
                  ( is-symmetric-neighborhood-ℝ (δf ε') xℝ yℝ Nμεxy))
          ≤ ( real-ℚ⁺ ε' *ℝ dist-ℝ xℝ yℝ) +ℝ
            ( real-ℚ⁺ ε' *ℝ dist-ℝ xℝ yℝ)
            by
              leq-eq-ℝ
                ( ap-add-ℝ (ap-mul-ℝ refl (commutative-dist-ℝ yℝ xℝ)) refl)
          ≤ (real-ℚ⁺ ε' +ℝ real-ℚ⁺ ε') *ℝ dist-ℝ xℝ yℝ
            by leq-eq-ℝ (inv (right-distributive-mul-add-ℝ _ _ _))
          ≤ real-ℚ⁺ (ε' +ℚ⁺ ε') *ℝ dist-ℝ xℝ yℝ
            by leq-eq-ℝ (ap-mul-ℝ (add-real-ℚ _ _) refl)
          ≤ real-ℚ⁺ ε *ℝ dist-ℝ xℝ yℝ
            by
              preserves-leq-right-mul-ℝ⁰⁺
                ( nonnegative-dist-ℝ xℝ yℝ)
                ( preserves-leq-real-ℚ (leq-le-ℚ ε'+ε'<ε))
          ≤ dist-ℝ xℝ yℝ *ℝ real-ℚ⁺ ε
            by leq-eq-ℝ (commutative-mul-ℝ _ _))

  is-uniformly-continuous-derivative-is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    is-uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f')
  is-uniformly-continuous-derivative-is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    is-uniformly-continuous-modulus-apart-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      { l5 = l1}
      ( V)
      ( [a,b])
      ( f')
      ( apart-modulus-is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
      ( is-apart-modulus-is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (df@(f , f' , Df) :
    differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b]))
  where

  abstract
    is-uniformly-continuous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
      is-uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b])
          ( df))
    is-uniformly-continuous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
      elim-exists
        ( is-uniformly-continuous-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b])
          ( f'))
        ( is-uniformly-continuous-derivative-is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b])
          ( f)
          ( f'))
        ( Df)

  uniformly-continuous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( l1)
      ( V)
      ( [a,b])
  uniformly-continuous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    ( f' ,
      is-uniformly-continuous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
```

### A differentiable map from a proper closed interval to a normed real vector space is uniformly continuous

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  ((f' , Df) :
    is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f))
  where abstract

  is-uniformly-continuous-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    is-uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f)
  is-uniformly-continuous-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    let
      open
        do-syntax-trunc-Prop
          ( is-uniformly-continuous-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
            ( V)
            ( [a,b])
            ( f))
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
      dist-V = dist-Normed-ℝ-Vector-Space V
      norm-V = map-norm-Normed-ℝ-Vector-Space V
      _-V_ = diff-Normed-ℝ-Vector-Space V
      _*V_ = mul-Normed-ℝ-Vector-Space V
      (max-|f'|⁰⁺@(max-|f'| , 0≤max-|f'|) , is-max-|f'|) =
        nonnegative-upper-bound-norm-im-uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b])
          ( uniformly-continuous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
            ( V)
            ( [a,b])
            ( f , f' , Df))
    in do
      (q , |f'|+1<q) ← exists-greater-positive-rational-ℝ (max-|f'| +ℝ one-ℝ)
      (δf' , is-mod-δf') ← Df
      let
        ωf ε = min-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε) (δf' one-ℚ⁺)
        is-mod-ωf :
          is-modulus-of-uniform-continuity-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
            ( V)
            ( [a,b])
            ( f)
            ( ωf)
        is-mod-ωf x ε y Nxy =
          chain-of-inequalities
            dist-V (f x) (f y)
            ≤ norm-V ((pr1 x -ℝ pr1 y) *V f' y) +ℝ
              dist-V (f x -V f y) ((pr1 x -ℝ pr1 y) *V f' y)
              by
                leq-norm-add-norm-dist-Normed-ℝ-Vector-Space
                  ( V)
                  ( f x -V f y)
                  ( (pr1 x -ℝ pr1 y) *V f' y)
            ≤ dist-ℝ (pr1 x) (pr1 y) *ℝ norm-V (f' y) +ℝ
              one-ℝ *ℝ dist-ℝ (pr1 x) (pr1 y)
              by
                preserves-leq-add-ℝ
                  ( leq-eq-ℝ
                    ( is-absolutely-homogeneous-norm-Normed-ℝ-Vector-Space V
                      ( _)
                      ( _)))
                  ( is-mod-δf'
                    ( one-ℚ⁺)
                    ( y)
                    ( x)
                    ( weakly-monotonic-neighborhood-ℝ
                      ( pr1 y)
                      ( pr1 x)
                      ( ωf ε)
                      ( δf' one-ℚ⁺)
                      ( leq-right-min-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε) (δf' one-ℚ⁺))
                      ( is-symmetric-neighborhood-ℝ
                        ( ωf ε)
                        ( pr1 x)
                        ( pr1 y)
                        ( Nxy))))
            ≤ norm-V (f' y) *ℝ dist-ℝ (pr1 x) (pr1 y) +ℝ
              one-ℝ *ℝ dist-ℝ (pr1 x) (pr1 y)
              by leq-eq-ℝ (ap-add-ℝ (commutative-mul-ℝ _ _) refl)
            ≤ (norm-V (f' y) +ℝ one-ℝ) *ℝ dist-ℝ (pr1 x) (pr1 y)
              by leq-eq-ℝ (inv (right-distributive-mul-add-ℝ _ _ _))
            ≤ (max-|f'| +ℝ one-ℝ) *ℝ real-ℚ⁺ (ωf ε)
              by
                preserves-leq-mul-ℝ⁰⁺
                  ( nonnegative-norm-Normed-ℝ-Vector-Space V (f' y) +ℝ⁰⁺
                    one-ℝ⁰⁺)
                  ( max-|f'|⁰⁺ +ℝ⁰⁺ one-ℝ⁰⁺)
                  ( nonnegative-dist-ℝ (pr1 x) (pr1 y))
                  ( nonnegative-real-ℚ⁺ (ωf ε))
                  ( preserves-leq-right-add-ℝ _ _ _ (is-max-|f'| y))
                  ( leq-dist-neighborhood-ℝ (ωf ε) (pr1 x) (pr1 y) Nxy)
            ≤ real-ℚ⁺ q *ℝ real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε)
              by
                preserves-leq-mul-ℝ⁰⁺
                  ( max-|f'|⁰⁺ +ℝ⁰⁺ one-ℝ⁰⁺)
                  ( nonnegative-real-ℚ⁺ q)
                  ( nonnegative-real-ℚ⁺ (ωf ε))
                  ( nonnegative-real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε))
                  ( leq-le-ℝ |f'|+1<q)
                  ( preserves-leq-real-ℚ
                    ( leq-left-min-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε) (δf' one-ℚ⁺)))
            ≤ real-ℚ⁺ (q *ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε))
              by leq-eq-ℝ (mul-real-ℚ _ _)
            ≤ real-ℚ⁺ ε
              by leq-eq-ℝ (ap real-ℚ (is-section-left-div-ℚ⁺ q _))
      intro-exists ωf is-mod-ωf

module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (df@(f , Df) :
    differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b]))
  where

  abstract
    is-uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
      is-uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b])
          ( df))
    is-uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
      is-uniformly-continuous-is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( f)
        ( Df)

  uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( l1)
      ( V)
      ( [a,b])
  uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    ( f ,
      is-uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
```
