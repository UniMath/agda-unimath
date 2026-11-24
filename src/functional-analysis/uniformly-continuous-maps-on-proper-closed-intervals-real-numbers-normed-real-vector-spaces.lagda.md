# Uniformly continuous maps from proper closed intervals in the real numbers to normed real vector spaces

```agda
module functional-analysis.uniformly-continuous-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.inhabited-subtypes
open import foundation.subtypes
open import foundation.universe-levels

open import functional-analysis.modulated-uniformly-continuous-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces

open import linear-algebra.normed-real-vector-spaces

open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.apartness-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.uniformly-continuous-real-maps-proper-closed-intervals-real-numbers
```

</details>

## Idea

A map `f` from a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
`[a, b]` in the [real numbers](real-numbers.dedekind-real-numbers.md) to a
[normed real vector space](linear-algebra.normed-real-vector-spaces.md) `V` is
{{#concept "uniformly continuous" Disambiguation="uniformly continuous map from a proper closed interval in ℝ to a normed real vector space" Agda=uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space}}
if it is
[uniformly continuous](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
as a map from the [metric space](metric-spaces.metric-spaces.md) of `[a, b]` to
the metric space of `V`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l3 l4)
  where

  is-uniformly-continuous-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    {l5 : Level} →
    subtype
      ( l1 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
      ( type-proper-closed-interval-ℝ l5 [a,b] → type-Normed-ℝ-Vector-Space V)
  is-uniformly-continuous-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
    f =
    is-inhabited-subtype-Prop
      ( is-modulus-of-uniform-continuity-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( f))

  is-uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    {l5 : Level} →
    (type-proper-closed-interval-ℝ l5 [a,b] → type-Normed-ℝ-Vector-Space V) →
    UU (l1 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
  is-uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    is-in-subtype
      ( is-uniformly-continuous-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
  {l1 l2 l3 l4 : Level} (l5 : Level) → Normed-ℝ-Vector-Space l1 l2 →
  proper-closed-interval-ℝ l3 l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
  l5 V [a,b] =
  type-subtype
    ( is-uniformly-continuous-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      { l5 = l5})
```

## Properties

### To show a function on a proper closed interval of real numbers is uniformly continuous, it suffices to exhibit a modulus that applies when its arguments are apart

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l3 l4)
  (f :
    type-proper-closed-interval-ℝ (l3 ⊔ l4 ⊔ l5) [a,b] →
    type-Normed-ℝ-Vector-Space V)
  (μ : ℚ⁺ → ℚ⁺)
  (H :
    (ε : ℚ⁺) (x y : type-proper-closed-interval-ℝ (l3 ⊔ l4 ⊔ l5) [a,b]) →
    apart-ℝ (pr1 x) (pr1 y) →
    neighborhood-ℝ _ (μ ε) (pr1 x) (pr1 y) →
    neighborhood-Normed-ℝ-Vector-Space V ε (f x) (f y))
  where abstract

  is-uniformly-continuous-modulus-apart-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    is-uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f)
  is-uniformly-continuous-modulus-apart-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    intro-exists
      ( modulus-modulus-apart-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        { l5 = l5}
        ( V)
        ( [a,b])
        ( f)
        ( μ)
        ( H))
      ( is-modulus-of-uniform-continuity-modulus-modulus-apart-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        { l5 = l5}
        ( V)
        ( [a,b])
        ( f)
        ( μ)
        ( H))
```

### There is a bound on the norm of the image of a proper closed interval under a uniformly continuous real function

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (ucf@(f , is-uc-f) :
    uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( l1)
      ( V)
      ( [a,b]))
  where abstract

  nonnegative-upper-bound-norm-im-uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    Σ ( ℝ⁰⁺ l1)
      ( λ b →
        (x : type-proper-closed-interval-ℝ l1 [a,b]) →
        leq-ℝ⁰⁺ (nonnegative-norm-Normed-ℝ-Vector-Space V (f x)) b)
  nonnegative-upper-bound-norm-im-uniformly-continuous-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    let
      (b , |||fx|||≤b) =
        nonnegative-upper-bound-abs-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
          ( [a,b])
          ( comp-uniformly-continuous-map-Metric-Space
            ( metric-space-proper-closed-interval-ℝ l1 [a,b])
            ( metric-space-Normed-ℝ-Vector-Space V)
            ( metric-space-ℝ l1)
            ( uniformly-continuous-map-norm-Normed-ℝ-Vector-Space V)
            ( ucf))
    in
      ( b ,
        λ x →
          transitive-leq-ℝ⁰⁺
            ( nonnegative-norm-Normed-ℝ-Vector-Space V (f x))
            ( nonnegative-abs-ℝ (map-norm-Normed-ℝ-Vector-Space V (f x)))
            ( b)
            ( |||fx|||≤b x)
            ( leq-abs-ℝ (map-norm-Normed-ℝ-Vector-Space V (f x))))
```

## See also

- [Modulated uniformly continuous maps from proper closed intervals in ℝ to normed real vector spaces](functional-analysis.modulated-uniformly-continuous-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces.md)
