# Modulated uniformly continuous maps from proper closed intervals in the real numbers to normed real vector spaces

```agda
module functional-analysis.modulated-uniformly-continuous-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.normed-real-vector-spaces

open import metric-spaces.modulated-uniformly-continuous-maps-metric-spaces

open import order-theory.large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.apartness-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

Given a map `f` from a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
`[a, b]` in the [real numbers](real-numbers.dedekind-real-numbers.md) to a
[normed real vector space](linear-algebra.normed-real-vector-spaces.md) `V`, a
{{#concept "modulus of uniform continuity" Disambiguation="for a map from a proper closed interval in ℝ to a normed real vector space" Agda=is-modulus-of-uniform-continuity-map-proper-closed-interval-real-Normed-ℝ-Vector-Space}}
for `f` is a
[modulus of uniform continuity](metric-spaces.modulated-uniformly-continuous-maps-metric-spaces.md)
of `f` from the [metric space](metric-spaces.metric-spaces.md) of `[a, b]` to
the metric space of `V`.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l3 l4)
  (f : type-proper-closed-interval-ℝ l5 [a,b] → type-Normed-ℝ-Vector-Space V)
  where

  is-modulus-of-uniform-continuity-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    subtype (l1 ⊔ l3 ⊔ l4 ⊔ lsuc l5) (ℚ⁺ → ℚ⁺)
  is-modulus-of-uniform-continuity-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    is-modulus-of-uniform-continuity-prop-map-Metric-Space
      ( metric-space-proper-closed-interval-ℝ l5 [a,b])
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( f)

  is-modulus-of-uniform-continuity-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    (ℚ⁺ → ℚ⁺) → UU (l1 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
  is-modulus-of-uniform-continuity-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    is-in-subtype
      ( is-modulus-of-uniform-continuity-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  modulus-of-uniform-continuity-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    UU (l1 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
  modulus-of-uniform-continuity-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    type-subtype
      ( is-modulus-of-uniform-continuity-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
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

  modulus-modulus-apart-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    ℚ⁺ → ℚ⁺
  modulus-modulus-apart-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    μ ∘ modulus-le-double-le-ℚ⁺

  is-modulus-of-uniform-continuity-modulus-modulus-apart-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    is-modulus-of-uniform-continuity-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f)
      ( modulus-modulus-apart-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
  is-modulus-of-uniform-continuity-modulus-modulus-apart-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
    x ε y Nxy =
    let
      (ε' , 2ε'<ε) = bound-double-le-ℚ⁺ ε
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in
      elim-exists
        ( neighborhood-prop-Normed-ℝ-Vector-Space V ε (f x) (f y))
        ( λ z (z#x , z#y , Nε'zx , Nε'zy) →
          chain-of-inequalities
            dist-Normed-ℝ-Vector-Space V (f x) (f y)
            ≤ dist-Normed-ℝ-Vector-Space V (f x) (f z) +ℝ
              dist-Normed-ℝ-Vector-Space V (f z) (f y)
              by triangular-dist-Normed-ℝ-Vector-Space V (f x) (f z) (f y)
            ≤ real-ℚ⁺ ε' +ℝ real-ℚ⁺ ε'
              by
                preserves-leq-add-ℝ
                  ( H ε' x z
                    ( symmetric-apart-ℝ z#x)
                    ( is-symmetric-neighborhood-ℝ (μ ε') (pr1 z) (pr1 x) Nε'zx))
                  ( H ε' z y z#y Nε'zy)
            ≤ real-ℚ⁺ (ε' +ℚ⁺ ε')
              by leq-eq-ℝ (add-real-ℚ _ _)
            ≤ real-ℚ⁺ ε
              by preserves-leq-real-ℚ (leq-le-ℚ 2ε'<ε))
        ( exists-element-apart-from-both-in-neighborhood-proper-closed-interval-ℝ
          ( l3 ⊔ l4 ⊔ l5)
          ( [a,b])
          ( x)
          ( y)
          ( μ ε')
          ( Nxy))
```
