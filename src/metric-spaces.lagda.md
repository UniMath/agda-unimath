# Metric spaces

## Idea

[Classical metric spaces](https://en.wikipedia.org/wiki/Metric_space#Definition)
are sets equipped with a positive definite, symmetric, reflexive, and triangular
binary map into the real numbers. Here, we follow {{#cite Booij2020PhD}} and
define a [premetric structure](metric-spaces.premetric-structures.md) on a type
as a family of
[propositition valued binary relations](foundation.binary-relations.md) indexed
by the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md).

Given a premetric

```text
  B : ℚ⁺ → A → A → Prop l
```

on a type `A`, the type of `B d x y` is called a `d`-neigborhood of `x` and `y`
and if it is inhabited we interpret `d` as an upper bound on the distance
between `x` and `y` in the premetric `B`.

In this context, a [metric space](metric-spaces.metric-spaces.md) is a type
equipped with a [reflexive](metric-spaces.reflexive-premetric-structures.md),
[symmetric](metric-spaces.symmetric-premetric-structures.md),
[triangular](metric-spaces.triangular-premetric-structures.md), and
[local](metric-spaces.extensional-premetric-structures.md) premetric structure:
a [metric structure](metric-spaces.metric-structures.md).

[Short maps](metric-spaces.short-functions-metric-spaces.md) and
[isometries](metric-spaces.isometries-metric-spaces.md) are homomorphisms
between metric spaces and define the
[category of metric space and short maps](metric-spaces.category-of-metric-spaces-and-short-functions.md)
and the
[category of metric spaces and isometries](metric-spaces.category-of-metric-spaces-and-isometries.md).

## Instances of metric spaces

{{#include tables/metric-spaces.md}}

## Modules in the metric spaces namespace

```agda
module metric-spaces where

open import metric-spaces.category-of-metric-spaces-and-isometries public
open import metric-spaces.category-of-metric-spaces-and-short-functions public
open import metric-spaces.cauchy-approximations-metric-spaces public
open import metric-spaces.cauchy-approximations-premetric-spaces public
open import metric-spaces.closed-premetric-structures public
open import metric-spaces.complete-metric-spaces public
open import metric-spaces.convergent-cauchy-approximations-metric-spaces public
open import metric-spaces.dependent-products-metric-spaces public
open import metric-spaces.discrete-premetric-structures public
open import metric-spaces.equality-of-metric-spaces public
open import metric-spaces.equality-of-premetric-spaces public
open import metric-spaces.extensional-premetric-structures public
open import metric-spaces.functions-metric-spaces public
open import metric-spaces.functor-category-set-functions-isometry-metric-spaces public
open import metric-spaces.functor-category-short-isometry-metric-spaces public
open import metric-spaces.induced-premetric-structures-on-preimages public
open import metric-spaces.invertible-isometries-premetric-spaces public
open import metric-spaces.isometric-equivalences-premetric-spaces public
open import metric-spaces.isometries-metric-spaces public
open import metric-spaces.isometries-premetric-spaces public
open import metric-spaces.limits-of-cauchy-approximations-in-premetric-spaces public
open import metric-spaces.metric-space-of-cauchy-approximations-in-a-metric-space public
open import metric-spaces.metric-space-of-convergent-cauchy-approximations-in-a-metric-space public
open import metric-spaces.metric-space-of-rational-numbers public
open import metric-spaces.metric-space-of-rational-numbers-with-open-neighborhoods public
open import metric-spaces.metric-spaces public
open import metric-spaces.metric-structures public
open import metric-spaces.monotonic-premetric-structures public
open import metric-spaces.ordering-premetric-structures public
open import metric-spaces.precategory-of-metric-spaces-and-functions public
open import metric-spaces.precategory-of-metric-spaces-and-isometries public
open import metric-spaces.precategory-of-metric-spaces-and-short-functions public
open import metric-spaces.premetric-spaces public
open import metric-spaces.premetric-structures public
open import metric-spaces.pseudometric-spaces public
open import metric-spaces.pseudometric-structures public
open import metric-spaces.reflexive-premetric-structures public
open import metric-spaces.saturated-metric-spaces public
open import metric-spaces.short-functions-metric-spaces public
open import metric-spaces.short-functions-premetric-spaces public
open import metric-spaces.subspaces-metric-spaces public
open import metric-spaces.symmetric-premetric-structures public
open import metric-spaces.triangular-premetric-structures public
```

## References

{{#bibliography}}
