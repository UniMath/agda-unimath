# Differentiable maps from proper closed intervals on ℝ to normed real vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
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

open import linear-algebra.normed-real-vector-spaces

open import lists.sequences

open import metric-spaces.limits-of-sequences-metric-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.accumulation-points-subsets-real-numbers
open import real-numbers.apartness-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-nonzero-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.nonzero-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
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
