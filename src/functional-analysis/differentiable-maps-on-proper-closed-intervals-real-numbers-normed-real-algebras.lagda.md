# Differentiable maps from proper closed intervals in the real numbers to normed real algebras

```agda
module functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-algebras where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces

open import linear-algebra.normed-real-algebras

open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import real-numbers.proper-closed-intervals-real-numbers
```

</details>

## Idea

Given a map `f` from a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
`[a, b]` of [real numbers](real-numbers.dedekind-real-numbers.md) to a
[normed real algebra](linear-algebra.normed-real-algebras.md) `A`, `g` is a
{{#concept "derivative" Disambiguation="of map from a proper closed interval in ℝ to a normed real algebra" Agda=is-derivative-map-proper-closed-interval-real-Normed-ℝ-Algebra}}
of `f` if there [exists](foundation.existential-quantification.md) a modulus
function `μ` such that for `ε : ℚ⁺` and any `x` and `y` in `[a, b]` within a
`μ(ε)`-[neighborhood](real-numbers.metric-space-of-real-numbers.md) of each
other, we have $$∥f(y) - f(x) - (y - x)g(x)∥ ≤ ε|y - x|.$$

## Definition

```agda
module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f g : type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Algebra A)
  where

  is-modulus-of-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    subtype (lsuc l1) (ℚ⁺ → ℚ⁺)
  is-modulus-of-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    is-modulus-of-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( normed-vector-space-Normed-ℝ-Algebra A)
      ( [a,b])
      ( f)
      ( g)

  is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    (ℚ⁺ → ℚ⁺) → UU (lsuc l1)
  is-modulus-of-derivative-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    is-in-subtype
      ( is-modulus-of-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra)

  is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    Prop (lsuc l1)
  is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( normed-vector-space-Normed-ℝ-Algebra A)
      ( [a,b])
      ( f)
      ( g)

  is-derivative-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    UU (lsuc l1)
  is-derivative-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    type-Prop
      ( is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra)

module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  where

  is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    subtype
      ( lsuc l1 ⊔ l2)
      ( type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Algebra A)
  is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( normed-vector-space-Normed-ℝ-Algebra A)
      ( [a,b])

  is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    (type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Algebra A) →
    UU (lsuc l1 ⊔ l2)
  is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    is-in-subtype
      ( is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra)

  differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    UU (lsuc l1 ⊔ l2)
  differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    type-subtype
      ( is-differentiable-prop-map-proper-closed-interval-real-Normed-ℝ-Algebra)

module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  (let vec-space-A = normed-vector-space-Normed-ℝ-Algebra A)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  ((f , f' , Df) :
    differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra A [a,b])
  where

  map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Algebra A
  map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra = f

  uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    uniformly-continuous-map-Metric-Space
      ( metric-space-proper-closed-interval-ℝ l1 [a,b])
      ( metric-space-Normed-ℝ-Algebra A)
  uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( vec-space-A)
      ( [a,b])
      ( f , f' , Df)

  is-uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    is-uniformly-continuous-map-Metric-Space
      ( metric-space-proper-closed-interval-ℝ l1 [a,b])
      ( metric-space-Normed-ℝ-Algebra A)
      ( map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra)
  is-uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    pr2
      ( uniformly-continuous-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra)

  is-differentiable-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra
      ( A)
      ( [a,b])
      ( map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra)
  is-differentiable-map-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    ( f' , Df)

  map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Algebra A
  map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    f'

  uniformly-continuous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    uniformly-continuous-map-Metric-Space
      ( metric-space-proper-closed-interval-ℝ l1 [a,b])
      ( metric-space-Normed-ℝ-Algebra A)
  uniformly-continuous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    uniformly-continuous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( vec-space-A)
      ( [a,b])
      ( f , f' , Df)

  is-uniformly-continuous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra :
    is-uniformly-continuous-map-Metric-Space
      ( metric-space-proper-closed-interval-ℝ l1 [a,b])
      ( metric-space-Normed-ℝ-Algebra A)
      ( map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra)
  is-uniformly-continuous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra =
    pr2
      ( uniformly-continuous-map-derivative-differentiable-map-proper-closed-interval-real-Normed-ℝ-Algebra)
```
