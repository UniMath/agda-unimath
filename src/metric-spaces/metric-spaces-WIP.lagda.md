# Metric spaces (WIP)

```agda
module metric-spaces.metric-spaces-WIP where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.extensional-premetric-spaces-WIP
open import metric-spaces.premetric-spaces-WIP
open import metric-spaces.same-neighbors-elements-premetric-spaces
open import metric-spaces.similarity-of-elements-premetric-spaces
```

</details>

## Idea

A
{{#concept "metric space" Agda=Metric-Space-WIP WD="metric space" WDID=Q180953}}
is a type [structured](foundation.structure.md) with a concept of distance on
its elements.

Since we operate in a constructive setting, the concept of distance is captured
by considering upper bounds on the distance between points, rather than by a
distance function as in the classical approach. Thus, a metric space `A` is
defined by a family of _neighborhood_
[relations](foundation.binary-relations.md) on it indexed by the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
`ℚ⁺`, a
[rational neighborhood relation](metric-spaces.rational-neighborhoods.md):

```text
  N : ℚ⁺ → A → A → Prop l
```

that satisfies certain axioms. Constructing a proof of `N d x y` amounts to
saying that _`d` is an upper bound on the distance from `x` to `y`_.

The neighborhood relation on a metric space must satisfy the following axioms:

- [**Reflexivity.**](metric-spaces.reflexive-rational-neighborhoods.md) Every
  positive rational `d` is an upper bound on the distance from `x` to itself.
- [**Symmetry.**](metric-spaces.symmetric-rational-neighborhoods.md) Any upper
  bound on the distance from `x` to `y` is an upper bound on the distance from
  `y` to `x`.
- [**Triangularity.**](metric-spaces.triangular-rational-neighborhoods.md) If
  `d` is an upper bound on the distance from `x` to `y`, and `d'` is an upper
  bound on the distance from `y` to `z`, then `d + d'` is an upper bound on the
  distance from `x` to `z`.

This gives `A` the structure of a
[**premetric space**](metric-spaces.premetric-spaces-WIP.md); finally, we ask
that our metric spaces are
[**extensional**](metric-spaces.extensional-premetric-spaces-WIP.md):
[similar](metric-spaces.similarity-of-elements-premetric-spaces.md) elements are
[equal](foundation-core.identity-types.md):

- If every positive rational `d` is an upper bound on the distance from `x` to
  `y`, then `x ＝ y`.

Similarity of elements in a metric space characterizes their equality so any
metric space is a [set](foundation.sets.md).

## Definitions

### The type of metric spaces

```agda
Metric-Space-WIP : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Metric-Space-WIP l1 l2 =
  type-subtype (is-extensional-prop-Premetric-Space-WIP {l1} {l2})

module _
  {l1 l2 : Level} (M : Metric-Space-WIP l1 l2)
  where

  premetric-Metric-Space-WIP : Premetric-Space-WIP l1 l2
  premetric-Metric-Space-WIP = pr1 M

  is-extensional-premetric-Metric-Space-WIP :
    is-extensional-Premetric-Space-WIP premetric-Metric-Space-WIP
  is-extensional-premetric-Metric-Space-WIP = pr2 M

  type-Metric-Space-WIP : UU l1
  type-Metric-Space-WIP =
    type-Premetric-Space-WIP premetric-Metric-Space-WIP

  structure-Metric-Space-WIP : Premetric-Structure l2 type-Metric-Space-WIP
  structure-Metric-Space-WIP =
    structure-Premetric-Space-WIP premetric-Metric-Space-WIP

  neighborhood-prop-Metric-Space-WIP :
    ℚ⁺ → Relation-Prop l2 type-Metric-Space-WIP
  neighborhood-prop-Metric-Space-WIP =
    neighborhood-prop-Premetric-Space-WIP premetric-Metric-Space-WIP

  neighborhood-Metric-Space-WIP : ℚ⁺ → Relation l2 type-Metric-Space-WIP
  neighborhood-Metric-Space-WIP =
    neighborhood-Premetric-Space-WIP premetric-Metric-Space-WIP

  is-prop-neighborhood-Metric-Space-WIP :
    (d : ℚ⁺) (x y : type-Metric-Space-WIP) →
    is-prop (neighborhood-Metric-Space-WIP d x y)
  is-prop-neighborhood-Metric-Space-WIP =
    is-prop-neighborhood-Premetric-Space-WIP premetric-Metric-Space-WIP

  is-upper-bound-dist-Metric-Space-WIP :
    (x y : type-Metric-Space-WIP) → ℚ⁺ → UU l2
  is-upper-bound-dist-Metric-Space-WIP x y d =
    neighborhood-Metric-Space-WIP d x y

  is-prop-is-upper-bound-dist-Metric-Space-WIP :
    (x y : type-Metric-Space-WIP) (d : ℚ⁺) →
    is-prop (is-upper-bound-dist-Metric-Space-WIP x y d)
  is-prop-is-upper-bound-dist-Metric-Space-WIP x y d =
    is-prop-neighborhood-Metric-Space-WIP d x y

  is-premetric-neighborhood-Metric-Space-WIP :
    is-premetric-Rational-Neighborhood-Relation
      type-Metric-Space-WIP
      neighborhood-prop-Metric-Space-WIP
  is-premetric-neighborhood-Metric-Space-WIP =
    is-premetric-neighborhood-Premetric-Space-WIP
      premetric-Metric-Space-WIP

  refl-neighborhood-Metric-Space-WIP :
    (d : ℚ⁺) (x : type-Metric-Space-WIP) →
    neighborhood-Metric-Space-WIP d x x
  refl-neighborhood-Metric-Space-WIP =
    refl-neighborhood-Premetric-Space-WIP premetric-Metric-Space-WIP

  symmetric-neighborhood-Metric-Space-WIP :
    (d : ℚ⁺) (x y : type-Metric-Space-WIP) →
    neighborhood-Metric-Space-WIP d x y →
    neighborhood-Metric-Space-WIP d y x
  symmetric-neighborhood-Metric-Space-WIP =
    symmetric-neighborhood-Premetric-Space-WIP premetric-Metric-Space-WIP

  inv-neighborhood-Metric-Space-WIP :
    {d : ℚ⁺} {x y : type-Metric-Space-WIP} →
    neighborhood-Metric-Space-WIP d x y →
    neighborhood-Metric-Space-WIP d y x
  inv-neighborhood-Metric-Space-WIP =
    inv-neighborhood-Premetric-Space-WIP premetric-Metric-Space-WIP

  triangular-neighborhood-Metric-Space-WIP :
    (x y z : type-Metric-Space-WIP) (d₁ d₂ : ℚ⁺) →
    neighborhood-Metric-Space-WIP d₂ y z →
    neighborhood-Metric-Space-WIP d₁ x y →
    neighborhood-Metric-Space-WIP (d₁ +ℚ⁺ d₂) x z
  triangular-neighborhood-Metric-Space-WIP =
    triangular-neighborhood-Premetric-Space-WIP premetric-Metric-Space-WIP

  monotonic-neighborhood-Metric-Space-WIP :
    (x y : type-Metric-Space-WIP) (d₁ d₂ : ℚ⁺) →
    le-ℚ⁺ d₁ d₂ →
    neighborhood-Metric-Space-WIP d₁ x y →
    neighborhood-Metric-Space-WIP d₂ x y
  monotonic-neighborhood-Metric-Space-WIP =
    monotonic-neighborhood-Premetric-Space-WIP premetric-Metric-Space-WIP
```

### Similarity of elements in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  where

  sim-prop-Metric-Space-WIP : Relation-Prop l2 (type-Metric-Space-WIP A)
  sim-prop-Metric-Space-WIP =
    sim-prop-Premetric-Space-WIP (premetric-Metric-Space-WIP A)

  sim-Metric-Space-WIP : Relation l2 (type-Metric-Space-WIP A)
  sim-Metric-Space-WIP =
    sim-Premetric-Space-WIP (premetric-Metric-Space-WIP A)

  is-prop-sim-Metric-Space-WIP :
    (x y : type-Metric-Space-WIP A) →
    is-prop (sim-Metric-Space-WIP x y)
  is-prop-sim-Metric-Space-WIP =
    is-prop-sim-Premetric-Space-WIP (premetric-Metric-Space-WIP A)

  refl-sim-Metric-Space-WIP :
    (x : type-Metric-Space-WIP A) →
    sim-Metric-Space-WIP x x
  refl-sim-Metric-Space-WIP =
    refl-sim-Premetric-Space-WIP (premetric-Metric-Space-WIP A)

  sim-eq-Metric-Space-WIP :
    (x y : type-Metric-Space-WIP A) →
    x ＝ y →
    sim-Metric-Space-WIP x y
  sim-eq-Metric-Space-WIP =
    sim-eq-Premetric-Space-WIP (premetric-Metric-Space-WIP A)

  symmetric-sim-Metric-Space-WIP :
    (x y : type-Metric-Space-WIP A) →
    sim-Metric-Space-WIP x y →
    sim-Metric-Space-WIP y x
  symmetric-sim-Metric-Space-WIP =
    symmetric-sim-Premetric-Space-WIP (premetric-Metric-Space-WIP A)

  inv-sim-Metric-Space-WIP :
    {x y : type-Metric-Space-WIP A} →
    sim-Metric-Space-WIP x y →
    sim-Metric-Space-WIP y x
  inv-sim-Metric-Space-WIP {x} {y} =
    inv-sim-Premetric-Space-WIP (premetric-Metric-Space-WIP A)

  transitive-sim-Metric-Space-WIP :
    (x y z : type-Metric-Space-WIP A) →
    sim-Metric-Space-WIP y z →
    sim-Metric-Space-WIP x y →
    sim-Metric-Space-WIP x z
  transitive-sim-Metric-Space-WIP =
    transitive-sim-Premetric-Space-WIP (premetric-Metric-Space-WIP A)

  equivalence-sim-Metric-Space-WIP :
    equivalence-relation l2 (type-Metric-Space-WIP A)
  equivalence-sim-Metric-Space-WIP =
    equivalence-sim-Premetric-Space-WIP (premetric-Metric-Space-WIP A)
```

```agda
module _
  {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  where

  sim-prop-Metric-Space-WIP' : Relation-Prop (l1 ⊔ l2) (type-Metric-Space-WIP A)
  sim-prop-Metric-Space-WIP' =
    sim-prop-Premetric-Space-WIP' (premetric-Metric-Space-WIP A)

  sim-Metric-Space-WIP' : Relation (l1 ⊔ l2) (type-Metric-Space-WIP A)
  sim-Metric-Space-WIP' =
    sim-Premetric-Space-WIP' (premetric-Metric-Space-WIP A)

  is-prop-sim-Metric-Space-WIP' :
    (x y : type-Metric-Space-WIP A) →
    is-prop (sim-Metric-Space-WIP' x y)
  is-prop-sim-Metric-Space-WIP' =
    is-prop-sim-Premetric-Space-WIP' (premetric-Metric-Space-WIP A)

  refl-sim-Metric-Space-WIP' :
    (x : type-Metric-Space-WIP A) →
    sim-Metric-Space-WIP' x x
  refl-sim-Metric-Space-WIP' =
    refl-sim-Premetric-Space-WIP' (premetric-Metric-Space-WIP A)

  sim-eq-Metric-Space-WIP' :
    (x y : type-Metric-Space-WIP A) →
    x ＝ y →
    sim-Metric-Space-WIP' x y
  sim-eq-Metric-Space-WIP' =
    sim-eq-Premetric-Space-WIP' (premetric-Metric-Space-WIP A)

  symmetric-sim-Metric-Space-WIP' :
    (x y : type-Metric-Space-WIP A) →
    sim-Metric-Space-WIP' x y →
    sim-Metric-Space-WIP' y x
  symmetric-sim-Metric-Space-WIP' =
    symmetric-sim-Premetric-Space-WIP' (premetric-Metric-Space-WIP A)

  inv-sim-Metric-Space-WIP' :
    {x y : type-Metric-Space-WIP A} →
    sim-Metric-Space-WIP' x y →
    sim-Metric-Space-WIP' y x
  inv-sim-Metric-Space-WIP' {x} {y} =
    inv-sim-Premetric-Space-WIP' (premetric-Metric-Space-WIP A)

  transitive-sim-Metric-Space-WIP' :
    (x y z : type-Metric-Space-WIP A) →
    sim-Metric-Space-WIP' y z →
    sim-Metric-Space-WIP' x y →
    sim-Metric-Space-WIP' x z
  transitive-sim-Metric-Space-WIP' =
    transitive-sim-Premetric-Space-WIP' (premetric-Metric-Space-WIP A)

  equivalence-sim-Metric-Space-Wip' :
    equivalence-relation (l1 ⊔ l2) (type-Metric-Space-WIP A)
  equivalence-sim-Metric-Space-Wip' =
    equivalence-sim-Premetric-Space-WIP' (premetric-Metric-Space-WIP A)
```

## Properties

### The carrier type of a metric space is a set

```agda
module _
  {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  where

  is-set-type-Metric-Space-WIP : is-set (type-Metric-Space-WIP A)
  is-set-type-Metric-Space-WIP =
    is-set-type-is-extensional-Premetric-Space-WIP
      ( premetric-Metric-Space-WIP A)
      ( is-extensional-premetric-Metric-Space-WIP A)

  set-Metric-Space-WIP : Set l1
  set-Metric-Space-WIP =
    (type-Metric-Space-WIP A , is-set-type-Metric-Space-WIP)
```

### Similarity of elements in a metric space is equivalent to equality

```agda
module _
  {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  where

  equiv-sim-eq-Metric-Space-WIP :
    (x y : type-Metric-Space-WIP A) →
    (x ＝ y) ≃ sim-Metric-Space-WIP' A x y
  equiv-sim-eq-Metric-Space-WIP =
    equiv-sim-eq-is-extensional-Premetric-Space-WIP
      ( premetric-Metric-Space-WIP A)
      ( is-extensional-premetric-Metric-Space-WIP A)

  eq-sim-Metric-Space-WIP :
    (x y : type-Metric-Space-WIP A) →
    sim-Metric-Space-WIP' A x y →
    x ＝ y
  eq-sim-Metric-Space-WIP x y =
    map-inv-equiv (equiv-sim-eq-Metric-Space-WIP x y)
```

## External links

- [`MetricSpaces.Type`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MetricSpaces.Type.html)
  at TypeTopology
- [metric space](https://ncatlab.org/nlab/show/metric+space) at $n$Lab
- [Metric spaces](https://en.wikipedia.org/wiki/Metric_space) at Wikipedia
