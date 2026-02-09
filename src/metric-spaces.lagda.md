# Metric spaces

## Idea

Metric spaces are types [structured](foundation.structure.md) with a concept of
distance on its elements.

Since we operate in a constructive setting, the concept of distance is captured
by considering upper bounds on the distance between points, rather than by a
distance function as in the classical approach. Thus, a metric space `A` is
defined by a family of
[neighborhood](metric-spaces.rational-neighborhood-relations.md)
[relations](foundation.binary-relations.md) on it indexed by the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
`ℚ⁺`,

```text
  N : ℚ⁺ → A → A → Prop l
```

that satisfies certain axioms. Constructing a proof of `N d x y` amounts to
saying that _`d` is an upper bound on the distance from `x` to `y`_.

The neighborhood relation on a metric space must satisfy the following axioms:

- [Reflexivity](metric-spaces.reflexive-rational-neighborhood-relations.md):
  every positive rational `d` is an upper bound on the distance from `x` to
  itself.
- [Symmetry](metric-spaces.symmetric-rational-neighborhood-relations.md): if `d`
  is an upper bound on the distance from `x` to `y`, then `d` is an upper bound
  on the distance from `y` to `x`.
- [Triangularity](metric-spaces.triangular-rational-neighborhood-relations.md):
  if `d` is an upper bound on the distance from `x` to `y`, and `d'` is an upper
  bound on the distance from `y` to `z`, then `d + d'` is an upper bound on the
  distance from `x` to `z`.

Finally, we ask that our metric spaces are
[extensional](metric-spaces.extensionality-pseudometric-spaces.md), which
amounts to the property of **indistinguishability of identicals**:

- If every positive rational `d` is an upper bound on the distance from `x` to
  `y`, then `x` and `y` are [equal](foundation-core.identity-types.md).

The relationship to a [real](real-numbers.dedekind-real-numbers.md)-valued
distance function, called a [metric](metric-spaces.metrics.md), can be recovered
[if and only if](foundation.logical-equivalences.md) every element of the metric
space is at
[bounded distance](metric-spaces.elements-at-bounded-distance-metric-spaces.md)
from every other element, and the metric space is
[located](metric-spaces.located-metric-spaces.md), that is, for every positive
rational `d₁` and `d₂` with `d₁ < d₂`, and every element `x` and `y` of the
metric space, `N d₂ x y` [or](foundation.disjunction.md)
[not](foundation.negation.md) `N d₁ x y`.

## Instances of metric spaces

{{#include tables/metric-spaces.md}}

## Modules in the metric spaces namespace

```agda
module metric-spaces where

open import metric-spaces.accumulation-points-subsets-located-metric-spaces public
open import metric-spaces.action-on-cauchy-approximations-isometries-pseudometric-spaces public
open import metric-spaces.action-on-cauchy-approximations-short-maps-metric-spaces public
open import metric-spaces.action-on-cauchy-approximations-short-maps-pseudometric-spaces public
open import metric-spaces.action-on-cauchy-sequences-short-maps-metric-spaces public
open import metric-spaces.action-on-cauchy-sequences-uniformly-continuous-maps-metric-spaces public
open import metric-spaces.action-on-convergent-sequences-modulated-uniformly-continuous-maps-metric-spaces public
open import metric-spaces.action-on-convergent-sequences-short-maps-metric-spaces public
open import metric-spaces.action-on-convergent-sequences-uniformly-continuous-maps-metric-spaces public
open import metric-spaces.action-on-modulated-cauchy-sequences-modulated-uniformly-continuous-maps-metric-spaces public
open import metric-spaces.apartness-located-metric-spaces public
open import metric-spaces.approximations-located-metric-spaces public
open import metric-spaces.approximations-metric-spaces public
open import metric-spaces.bounded-distance-decompositions-of-metric-spaces public
open import metric-spaces.cartesian-products-metric-spaces public
open import metric-spaces.category-of-metric-spaces-and-isometries public
open import metric-spaces.category-of-metric-spaces-and-short-maps public
open import metric-spaces.cauchy-approximations-in-cauchy-pseudocompletions-of-pseudometric-spaces public
open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces public
open import metric-spaces.cauchy-approximations-metric-spaces public
open import metric-spaces.cauchy-approximations-pseudometric-spaces public
open import metric-spaces.cauchy-pseudocompletion-of-complete-metric-spaces public
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces public
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces public
open import metric-spaces.cauchy-sequences-complete-metric-spaces public
open import metric-spaces.cauchy-sequences-metric-spaces public
open import metric-spaces.closed-subsets-located-metric-spaces public
open import metric-spaces.closed-subsets-metric-spaces public
open import metric-spaces.closure-subsets-metric-spaces public
open import metric-spaces.compact-metric-spaces public
open import metric-spaces.complete-metric-spaces public
open import metric-spaces.continuity-of-maps-at-points-metric-spaces public
open import metric-spaces.convergent-cauchy-approximations-metric-spaces public
open import metric-spaces.convergent-sequences-metric-spaces public
open import metric-spaces.dense-subsets-metric-spaces public
open import metric-spaces.dependent-products-complete-metric-spaces public
open import metric-spaces.dependent-products-metric-spaces public
open import metric-spaces.discrete-metric-spaces public
open import metric-spaces.elements-at-bounded-distance-metric-spaces public
open import metric-spaces.epsilon-delta-limits-of-maps-metric-spaces public
open import metric-spaces.equality-of-metric-spaces public
open import metric-spaces.equality-of-pseudometric-spaces public
open import metric-spaces.extensionality-pseudometric-spaces public
open import metric-spaces.functor-category-set-functions-isometry-metric-spaces public
open import metric-spaces.functor-category-short-isometry-metric-spaces public
open import metric-spaces.functoriality-isometries-metric-quotients-of-pseudometric-spaces public
open import metric-spaces.functoriality-short-maps-metric-quotients-of-pseudometric-spaces public
open import metric-spaces.images-isometries-metric-spaces public
open import metric-spaces.images-metric-spaces public
open import metric-spaces.images-short-maps-metric-spaces public
open import metric-spaces.images-uniformly-continuous-maps-metric-spaces public
open import metric-spaces.indexed-sums-metric-spaces public
open import metric-spaces.inhabited-totally-bounded-subspaces-metric-spaces public
open import metric-spaces.interior-subsets-metric-spaces public
open import metric-spaces.isometries-metric-spaces public
open import metric-spaces.isometries-pseudometric-spaces public
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces public
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces public
open import metric-spaces.limits-of-cauchy-sequences-metric-spaces public
open import metric-spaces.limits-of-maps-metric-spaces public
open import metric-spaces.limits-of-modulated-cauchy-sequences-metric-spaces public
open import metric-spaces.limits-of-sequences-metric-spaces public
open import metric-spaces.lipschitz-maps-metric-spaces public
open import metric-spaces.locally-constant-maps-metric-spaces public
open import metric-spaces.located-metric-spaces public
open import metric-spaces.maps-metric-spaces public
open import metric-spaces.maps-pseudometric-spaces public
open import metric-spaces.metric-quotients-of-metric-spaces public
open import metric-spaces.metric-quotients-of-pseudometric-spaces public
open import metric-spaces.metric-space-of-cauchy-approximations-complete-metric-spaces public
open import metric-spaces.metric-space-of-cauchy-approximations-metric-spaces public
open import metric-spaces.metric-space-of-convergent-cauchy-approximations-metric-spaces public
open import metric-spaces.metric-space-of-convergent-sequences-metric-spaces public
open import metric-spaces.metric-space-of-isometries-metric-spaces public
open import metric-spaces.metric-space-of-lipschitz-maps-metric-spaces public
open import metric-spaces.metric-space-of-maps-metric-spaces public
open import metric-spaces.metric-space-of-rational-numbers public
open import metric-spaces.metric-space-of-sequences-metric-spaces public
open import metric-spaces.metric-space-of-short-maps-metric-spaces public
open import metric-spaces.metric-spaces public
open import metric-spaces.metrics public
open import metric-spaces.metrics-of-metric-spaces public
open import metric-spaces.metrics-of-metric-spaces-are-uniformly-continuous public
open import metric-spaces.modulated-cauchy-sequences-complete-metric-spaces public
open import metric-spaces.modulated-cauchy-sequences-metric-spaces public
open import metric-spaces.modulated-uniformly-continuous-maps-metric-spaces public
open import metric-spaces.monotonic-rational-neighborhood-relations public
open import metric-spaces.nets-located-metric-spaces public
open import metric-spaces.nets-metric-spaces public
open import metric-spaces.open-subsets-located-metric-spaces public
open import metric-spaces.open-subsets-metric-spaces public
open import metric-spaces.pointwise-continuous-maps-metric-spaces public
open import metric-spaces.pointwise-epsilon-delta-continuous-maps-metric-spaces public
open import metric-spaces.poset-of-rational-neighborhood-relations public
open import metric-spaces.precategory-of-metric-spaces-and-isometries public
open import metric-spaces.precategory-of-metric-spaces-and-maps public
open import metric-spaces.precategory-of-metric-spaces-and-short-maps public
open import metric-spaces.preimages-rational-neighborhood-relations public
open import metric-spaces.pseudometric-spaces public
open import metric-spaces.rational-approximations-of-zero public
open import metric-spaces.rational-cauchy-approximations public
open import metric-spaces.rational-neighborhood-relations public
open import metric-spaces.rational-sequences-approximating-zero public
open import metric-spaces.reflexive-rational-neighborhood-relations public
open import metric-spaces.saturated-rational-neighborhood-relations public
open import metric-spaces.sequences-metric-spaces public
open import metric-spaces.short-maps-metric-spaces public
open import metric-spaces.short-maps-pseudometric-spaces public
open import metric-spaces.similarity-of-elements-pseudometric-spaces public
open import metric-spaces.subspaces-metric-spaces public
open import metric-spaces.symmetric-rational-neighborhood-relations public
open import metric-spaces.totally-bounded-metric-spaces public
open import metric-spaces.totally-bounded-subspaces-metric-spaces public
open import metric-spaces.triangular-rational-neighborhood-relations public
open import metric-spaces.uniform-homeomorphisms-metric-spaces public
open import metric-spaces.uniform-limit-theorem-pointwise-continuous-maps-metric-spaces public
open import metric-spaces.uniformly-continuous-maps-metric-spaces public
open import metric-spaces.unit-map-metric-quotients-of-pseudometric-spaces public
open import metric-spaces.universal-property-isometries-metric-quotients-of-pseudometric-spaces public
open import metric-spaces.universal-property-short-maps-metric-quotients-of-pseudometric-spaces public
```

## References

Our setup for metric space theory closely follows {{#cite Booij20PhD}}.

{{#bibliography}} {{#reference Booij20PhD}}
