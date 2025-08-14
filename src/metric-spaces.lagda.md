# Metric spaces

## Idea

Metric spaces are types [structured](foundation.structure.md) with a concept of
distance on its elements.

Since we operate in a constructive setting, the concept of distance is captured
by considering upper bounds on the distance between points, rather than by a
distance function as in the classical approach. Thus, a metric space `A` is
defined by a family of _neighborhood_
[relations](foundation.binary-relations.md) on it indexed by the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
`ℚ⁺`,

```text
  N : ℚ⁺ → A → A → Prop l
```

that satisfies certain axioms. Constructing a proof of `N d x y` amounts to
saying that _`d` is an upper bound on the distance from `x` to `y`_.

The neighborhood relation on a metric space must satisfy the following axioms:

- **Reflexivity.** Every positive rational `d` is an upper bound on the distance
  from `x` to itself.
- **Symmetry.** If `d` is an upper bound on the distance from `x` to `y`, then
  `d` is an upper bound on the distance from `y` to `x`.
- **Triangularity.** If `d` is an upper bound on the distance from `x` to `y`,
  and `d'` is an upper bound on the distance from `y` to `z`, then `d + d'` is
  an upper bound on the distance from `x` to `z`.

Finally, we ask that our metric spaces are **extensional**, which amounts to the
property of **indistinguishability of identicals**

- If every positive rational `d` is an upper bound on the distance from `x` to
  `y`, then `x` and `y` are [equal](foundation-core.identity-types.md).

## Instances of metric spaces

{{#include tables/metric-spaces.md}}

## Modules in the metric spaces namespace

```agda
module metric-spaces where

open import metric-spaces.category-of-metric-spaces-and-isometries public
open import metric-spaces.category-of-metric-spaces-and-short-functions public
open import metric-spaces.cauchy-approximations-metric-spaces public
open import metric-spaces.cauchy-approximations-pseudometric-spaces public
open import metric-spaces.cauchy-sequences-complete-metric-spaces public
open import metric-spaces.cauchy-sequences-metric-spaces public
open import metric-spaces.complete-metric-spaces public
open import metric-spaces.continuous-functions-metric-spaces public
open import metric-spaces.convergent-cauchy-approximations-metric-spaces public
open import metric-spaces.convergent-sequences-metric-spaces public
open import metric-spaces.dependent-products-metric-spaces public
open import metric-spaces.discrete-metric-spaces public
open import metric-spaces.elements-at-bounded-distance-metric-spaces public
open import metric-spaces.equality-of-metric-spaces public
open import metric-spaces.equality-of-pseudometric-spaces public
open import metric-spaces.extensionality-pseudometric-spaces public
open import metric-spaces.functions-metric-spaces public
open import metric-spaces.functions-pseudometric-spaces public
open import metric-spaces.functor-category-set-functions-isometry-metric-spaces public
open import metric-spaces.functor-category-short-isometry-metric-spaces public
open import metric-spaces.indexed-sums-metric-spaces public
open import metric-spaces.isometries-metric-spaces public
open import metric-spaces.isometries-pseudometric-spaces public
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces public
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces public
open import metric-spaces.limits-of-functions-metric-spaces public
open import metric-spaces.limits-of-sequences-metric-spaces public
open import metric-spaces.lipschitz-functions-metric-spaces public
open import metric-spaces.locally-constant-functions-metric-spaces public
open import metric-spaces.metric-space-of-cauchy-approximations-complete-metric-spaces public
open import metric-spaces.metric-space-of-cauchy-approximations-metric-spaces public
open import metric-spaces.metric-space-of-convergent-cauchy-approximations-metric-spaces public
open import metric-spaces.metric-space-of-convergent-sequences-metric-spaces public
open import metric-spaces.metric-space-of-functions-metric-spaces public
open import metric-spaces.metric-space-of-isometries-metric-spaces public
open import metric-spaces.metric-space-of-lipschitz-functions-metric-spaces public
open import metric-spaces.metric-space-of-rational-numbers public
open import metric-spaces.metric-space-of-short-functions-metric-spaces public
open import metric-spaces.metric-spaces public
open import metric-spaces.monotonic-rational-neighborhood-relations public
open import metric-spaces.poset-of-rational-neighborhood-relations public
open import metric-spaces.precategory-of-metric-spaces-and-functions public
open import metric-spaces.precategory-of-metric-spaces-and-isometries public
open import metric-spaces.precategory-of-metric-spaces-and-short-functions public
open import metric-spaces.preimages-rational-neighborhood-relations public
open import metric-spaces.pseudometric-spaces public
open import metric-spaces.rational-approximations-of-zero public
open import metric-spaces.rational-cauchy-approximations public
open import metric-spaces.rational-neighborhood-relations public
open import metric-spaces.rational-sequences-approximating-zero public
open import metric-spaces.reflexive-rational-neighborhood-relations public
open import metric-spaces.saturated-rational-neighborhood-relations public
open import metric-spaces.sequences-metric-spaces public
open import metric-spaces.short-functions-metric-spaces public
open import metric-spaces.similarity-of-elements-pseudometric-spaces public
open import metric-spaces.subspaces-metric-spaces public
open import metric-spaces.symmetric-rational-neighborhood-relations public
open import metric-spaces.triangular-rational-neighborhood-relations public
open import metric-spaces.uniformly-continuous-functions-metric-spaces public
```

## References

Our setup for metric space theory closely follows {{#cite Booij20PhD}}.

{{#bibliography}} {{#reference Booij20PhD}}
