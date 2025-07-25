# Metric spaces

```agda
module metric-spaces.metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.extensional-premetric-structures
open import metric-spaces.metric-structures
open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.premetric-spaces
open import metric-spaces.premetric-structures
open import metric-spaces.pseudometric-spaces
open import metric-spaces.pseudometric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

A {{#concept "metric space" Agda=Metric-Space WD="metric space" WDID=Q180953}}
is a type [structured](foundation.structure.md) with a concept of distance on
its elements.

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

Put concisely, a metric space is a
[premetric space](metric-spaces.premetric-spaces.md) whose
[premetric](metric-spaces.premetric-structures.md) is
[reflexive](metric-spaces.reflexive-premetric-structures.md),
[symmetric](metric-spaces.symmetric-premetric-structures.md),
[triangular](metric-spaces.triangular-premetric-structures.md), and
[extensional](metric-spaces.extensional-premetric-structures.md): a
[metric structure](metric-spaces.metric-structures.md). Equivalently, it is a
[pseudometric space](metric-spaces.pseudometric-spaces.md) whose premetric is
extensional.

## Definitions

### The property of being a metric premetric space

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  where

  is-metric-prop-Premetric-Space : Prop (l1 ⊔ l2)
  is-metric-prop-Premetric-Space =
    is-metric-prop-Premetric (structure-Premetric-Space A)

  is-metric-Premetric-Space : UU (l1 ⊔ l2)
  is-metric-Premetric-Space =
    type-Prop is-metric-prop-Premetric-Space

  is-prop-is-metric-Premetric-Space :
    is-prop is-metric-Premetric-Space
  is-prop-is-metric-Premetric-Space =
    is-prop-type-Prop is-metric-prop-Premetric-Space
```

### The type of metric spaces

```agda
Metric-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Metric-Space l1 l2 =
  type-subtype (is-metric-prop-Premetric-Space {l1} {l2})

module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  premetric-Metric-Space : Premetric-Space l1 l2
  premetric-Metric-Space = pr1 M

  type-Metric-Space : UU l1
  type-Metric-Space =
    type-Premetric-Space premetric-Metric-Space

  structure-Metric-Space : Premetric l2 type-Metric-Space
  structure-Metric-Space =
    structure-Premetric-Space premetric-Metric-Space

  is-metric-structure-Metric-Space :
    is-metric-Premetric structure-Metric-Space
  is-metric-structure-Metric-Space = pr2 M

  is-pseudometric-structure-Metric-Space :
    is-pseudometric-Premetric structure-Metric-Space
  is-pseudometric-structure-Metric-Space =
    is-pseudometric-is-metric-Premetric
      structure-Metric-Space
      is-metric-structure-Metric-Space

  pseudometric-Metric-Space : Pseudometric-Space l1 l2
  pseudometric-Metric-Space =
    premetric-Metric-Space , is-pseudometric-structure-Metric-Space

  neighborhood-Metric-Space : ℚ⁺ → Relation l2 type-Metric-Space
  neighborhood-Metric-Space =
    neighborhood-Premetric-Space premetric-Metric-Space

  is-upper-bound-dist-prop-Metric-Space :
    (x y : type-Metric-Space) → ℚ⁺ → Prop l2
  is-upper-bound-dist-prop-Metric-Space x y d =
    structure-Metric-Space d x y

  is-upper-bound-dist-Metric-Space :
    (x y : type-Metric-Space) → ℚ⁺ → UU l2
  is-upper-bound-dist-Metric-Space =
    is-upper-bound-dist-Premetric-Space premetric-Metric-Space

  is-reflexive-structure-Metric-Space :
    is-reflexive-Premetric structure-Metric-Space
  is-reflexive-structure-Metric-Space =
    is-reflexive-is-metric-Premetric
      structure-Metric-Space
      is-metric-structure-Metric-Space

  refl-structure-Metric-Space :
    is-reflexive-Premetric structure-Metric-Space
  refl-structure-Metric-Space =
    is-reflexive-is-metric-Premetric
      structure-Metric-Space
      is-metric-structure-Metric-Space

  is-symmetric-structure-Metric-Space :
    is-symmetric-Premetric structure-Metric-Space
  is-symmetric-structure-Metric-Space =
    is-symmetric-is-metric-Premetric
      structure-Metric-Space
      is-metric-structure-Metric-Space

  is-local-structure-Metric-Space :
    is-local-Premetric structure-Metric-Space
  is-local-structure-Metric-Space =
    is-local-is-metric-Premetric
      structure-Metric-Space
      is-metric-structure-Metric-Space

  is-triangular-structure-Metric-Space :
    is-triangular-Premetric structure-Metric-Space
  is-triangular-structure-Metric-Space =
    is-triangular-is-metric-Premetric
      structure-Metric-Space
      is-metric-structure-Metric-Space

  is-extensional-structure-Metric-Space :
    is-extensional-Premetric structure-Metric-Space
  is-extensional-structure-Metric-Space =
    is-reflexive-structure-Metric-Space ,
    is-local-structure-Metric-Space

  is-tight-structure-Metric-Space :
    is-tight-Premetric structure-Metric-Space
  is-tight-structure-Metric-Space =
    is-tight-is-extensional-Premetric
      structure-Metric-Space
      is-extensional-structure-Metric-Space

  is-monotonic-structure-Metric-Space :
    is-monotonic-Premetric structure-Metric-Space
  is-monotonic-structure-Metric-Space =
    is-monotonic-is-reflexive-triangular-Premetric
      structure-Metric-Space
      is-reflexive-structure-Metric-Space
      is-triangular-structure-Metric-Space

  is-set-type-Metric-Space : is-set type-Metric-Space
  is-set-type-Metric-Space =
    is-set-has-extensional-Premetric
      structure-Metric-Space
      is-extensional-structure-Metric-Space

  set-Metric-Space : Set l1
  set-Metric-Space = (type-Metric-Space , is-set-type-Metric-Space)

  is-indistinguishable-prop-Metric-Space : Relation-Prop l2 type-Metric-Space
  is-indistinguishable-prop-Metric-Space =
    is-indistinguishable-prop-Premetric-Space premetric-Metric-Space

  is-indistinguishable-Metric-Space : Relation l2 type-Metric-Space
  is-indistinguishable-Metric-Space =
    is-indistinguishable-Premetric-Space premetric-Metric-Space

  is-prop-is-indistinguishable-Metric-Space :
    (x y : type-Metric-Space) →
    is-prop (is-indistinguishable-Metric-Space x y)
  is-prop-is-indistinguishable-Metric-Space =
    is-prop-is-indistinguishable-Premetric-Space premetric-Metric-Space
```

## Properties

### Indistiguishability in a metric space is equivalent to equality

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x y : type-Metric-Space M)
  where

  equiv-indistinguishable-eq-Metric-Space :
    (x ＝ y) ≃ is-indistinguishable-Metric-Space M x y
  equiv-indistinguishable-eq-Metric-Space =
    equiv-eq-is-indistinguishable-is-extensional-Premetric
      ( structure-Metric-Space M)
      ( is-extensional-structure-Metric-Space M)

  indistinguishable-eq-Metric-Space :
    x ＝ y → is-indistinguishable-Metric-Space M x y
  indistinguishable-eq-Metric-Space =
    map-equiv equiv-indistinguishable-eq-Metric-Space

  eq-indistinguishable-Metric-Space :
    is-indistinguishable-Metric-Space M x y → x ＝ y
  eq-indistinguishable-Metric-Space =
    map-inv-equiv equiv-indistinguishable-eq-Metric-Space
```

### The type of metric spaces is equivalent to the type of extensional pseudometric spaces

#### The subtype of extensional pseudometric spaces

```agda
module _
  (l1 l2 : Level)
  where

  is-extensional-prop-Pseudometric-Space :
    subtype (l1 ⊔ l2) (Pseudometric-Space l1 l2)
  is-extensional-prop-Pseudometric-Space =
    is-local-prop-Premetric ∘ structure-Pseudometric-Space

  is-extensional-Pseudometric-Space :
    Pseudometric-Space l1 l2 → UU (l1 ⊔ l2)
  is-extensional-Pseudometric-Space =
    type-Prop ∘ is-extensional-prop-Pseudometric-Space

  is-prop-is-extensional-Pseudometric-Space :
    (M : Pseudometric-Space l1 l2) →
    is-prop (is-extensional-Pseudometric-Space M)
  is-prop-is-extensional-Pseudometric-Space =
    is-prop-type-Prop ∘ is-extensional-prop-Pseudometric-Space
```

## External links

- [`MetricSpaces.Type`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MetricSpaces.Type.html)
  at TypeTopology
- [metric space](https://ncatlab.org/nlab/show/metric+space) at $n$Lab
- [Metric spaces](https://en.wikipedia.org/wiki/Metric_space) at Wikipedia
