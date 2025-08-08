# Metric spaces

```agda
module metric-spaces.metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.extensional-pseudometric-spaces
open import metric-spaces.preimage-rational-neighborhoods
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhoods
open import metric-spaces.reflexive-rational-neighborhoods
open import metric-spaces.saturated-rational-neighborhoods
open import metric-spaces.similarity-of-elements-pseudometric-spaces
open import metric-spaces.symmetric-rational-neighborhoods
open import metric-spaces.triangular-rational-neighborhoods
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
- [**Saturation.**](metric-spaces.saturated-rational-neighborhoods.md): any
  neighborhood `N d x y` contains the intersection of all `N d' x y` for
  `d < d'`.

This gives `A` the structure of a
[**pseudometric space**](metric-spaces.pseudometric-spaces.md); finally, we ask
that our metric spaces are
[**extensional**](metric-spaces.extensional-pseudometric-spaces.md):
[similar](metric-spaces.similarity-of-elements-pseudometric-spaces.md) elements
are [equal](foundation-core.identity-types.md):

- If every positive rational `d` is an upper bound on the distance from `x` to
  `y`, then `x ＝ y`.

Similarity of elements in a metric space characterizes their equality so any
metric space is a [set](foundation.sets.md).

NB: When working with actual distance functions, the _saturation_ condition
always holds, defining `N d x y` as `dist(x , y) ≤ d`. Since we're working with
_upper bounds on distances_, we add this axiom to ensure that the subsets of
upper bounds on distances between elements is closed on the left.

## Definitions

### Metric Structures on a type

```agda
module _
  {l1 : Level} (A : UU l1) {l2 : Level}
  (B : Rational-Neighborhood-Relation l2 A)
  where

  is-metric-prop-Rational-Neighborhood-Relation : Prop (l1 ⊔ l2)
  is-metric-prop-Rational-Neighborhood-Relation =
    Σ-Prop
      ( is-pseudometric-prop-Rational-Neighborhood-Relation A B)
      ( λ H →
        is-extensional-prop-Pseudometric-Space (A , B , H))

  is-metric-Rational-Neighborhood-Relation : UU (l1 ⊔ l2)
  is-metric-Rational-Neighborhood-Relation =
    type-Prop is-metric-prop-Rational-Neighborhood-Relation

  is-prop-is-metric-Rational-Neighborhood-Relation :
    is-prop is-metric-Rational-Neighborhood-Relation
  is-prop-is-metric-Rational-Neighborhood-Relation =
    is-prop-type-Prop (is-metric-prop-Rational-Neighborhood-Relation)

Metric-Structure :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
Metric-Structure l2 A =
  type-subtype (is-metric-prop-Rational-Neighborhood-Relation A {l2})
```

### The type of metric spaces

```agda
Metric-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Metric-Space l1 l2 =
  Σ (UU l1) (Metric-Structure l2)

make-Metric-Space :
  { l1 l2 : Level} →
  ( A : UU l1) →
  ( B : Rational-Neighborhood-Relation l2 A) →
  ( refl-B : is-reflexive-Rational-Neighborhood-Relation B) →
  ( symmetric-B : is-symmetric-Rational-Neighborhood-Relation B) →
  ( triangular-B : is-triangular-Rational-Neighborhood-Relation B) →
  ( saturated-B : is-saturated-Rational-Neighborhood-Relation B) →
  ( extensional-B :
    is-extensional-Pseudometric-Space
      (A , B , refl-B , symmetric-B , triangular-B , saturated-B)) →
  Metric-Space l1 l2
make-Metric-Space
  A B refl-B symmetric-B triangular-B saturated-B extensional-B =
  ( A) ,
  ( ( B) ,
    ( refl-B , symmetric-B , triangular-B , saturated-B) ,
    ( extensional-B))

module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  type-Metric-Space : UU l1
  type-Metric-Space =
    pr1 M

  structure-Metric-Space : Metric-Structure l2 type-Metric-Space
  structure-Metric-Space = pr2 M

  pseudometric-Metric-Space : Pseudometric-Space l1 l2
  pseudometric-Metric-Space =
    ( type-Metric-Space) ,
    ( pr1 structure-Metric-Space) ,
    ( pr1 (pr2 structure-Metric-Space))

  is-extensional-pseudometric-Metric-Space :
    is-extensional-Pseudometric-Space pseudometric-Metric-Space
  is-extensional-pseudometric-Metric-Space =
    pr2 (pr2 structure-Metric-Space)

  pseudometric-structure-Metric-Space :
    Pseudometric-Structure l2 type-Metric-Space
  pseudometric-structure-Metric-Space =
    structure-Pseudometric-Space pseudometric-Metric-Space

  neighborhood-prop-Metric-Space :
    ℚ⁺ → Relation-Prop l2 type-Metric-Space
  neighborhood-prop-Metric-Space =
    neighborhood-prop-Pseudometric-Space pseudometric-Metric-Space

  neighborhood-Metric-Space : ℚ⁺ → Relation l2 type-Metric-Space
  neighborhood-Metric-Space =
    neighborhood-Pseudometric-Space pseudometric-Metric-Space

  is-prop-neighborhood-Metric-Space :
    (d : ℚ⁺) (x y : type-Metric-Space) →
    is-prop (neighborhood-Metric-Space d x y)
  is-prop-neighborhood-Metric-Space =
    is-prop-neighborhood-Pseudometric-Space pseudometric-Metric-Space

  is-upper-bound-dist-prop-Metric-Space :
    (x y : type-Metric-Space) → ℚ⁺ → Prop l2
  is-upper-bound-dist-prop-Metric-Space x y d =
    neighborhood-prop-Metric-Space d x y

  is-upper-bound-dist-Metric-Space :
    (x y : type-Metric-Space) → ℚ⁺ → UU l2
  is-upper-bound-dist-Metric-Space x y d =
    neighborhood-Metric-Space d x y

  is-prop-is-upper-bound-dist-Metric-Space :
    (x y : type-Metric-Space) (d : ℚ⁺) →
    is-prop (is-upper-bound-dist-Metric-Space x y d)
  is-prop-is-upper-bound-dist-Metric-Space x y d =
    is-prop-neighborhood-Metric-Space d x y

  is-pseudometric-neighborhood-Metric-Space :
    is-pseudometric-Rational-Neighborhood-Relation
      type-Metric-Space
      neighborhood-prop-Metric-Space
  is-pseudometric-neighborhood-Metric-Space =
    is-pseudometric-neighborhood-Pseudometric-Space
      pseudometric-Metric-Space

  refl-neighborhood-Metric-Space :
    (d : ℚ⁺) (x : type-Metric-Space) →
    neighborhood-Metric-Space d x x
  refl-neighborhood-Metric-Space =
    refl-neighborhood-Pseudometric-Space pseudometric-Metric-Space

  symmetric-neighborhood-Metric-Space :
    (d : ℚ⁺) (x y : type-Metric-Space) →
    neighborhood-Metric-Space d x y →
    neighborhood-Metric-Space d y x
  symmetric-neighborhood-Metric-Space =
    symmetric-neighborhood-Pseudometric-Space pseudometric-Metric-Space

  inv-neighborhood-Metric-Space :
    {d : ℚ⁺} {x y : type-Metric-Space} →
    neighborhood-Metric-Space d x y →
    neighborhood-Metric-Space d y x
  inv-neighborhood-Metric-Space =
    inv-neighborhood-Pseudometric-Space pseudometric-Metric-Space

  triangular-neighborhood-Metric-Space :
    (x y z : type-Metric-Space) (d₁ d₂ : ℚ⁺) →
    neighborhood-Metric-Space d₂ y z →
    neighborhood-Metric-Space d₁ x y →
    neighborhood-Metric-Space (d₁ +ℚ⁺ d₂) x z
  triangular-neighborhood-Metric-Space =
    triangular-neighborhood-Pseudometric-Space pseudometric-Metric-Space

  monotonic-neighborhood-Metric-Space :
    (x y : type-Metric-Space) (d₁ d₂ : ℚ⁺) →
    le-ℚ⁺ d₁ d₂ →
    neighborhood-Metric-Space d₁ x y →
    neighborhood-Metric-Space d₂ x y
  monotonic-neighborhood-Metric-Space =
    monotonic-neighborhood-Pseudometric-Space pseudometric-Metric-Space

  weakly-monotonic-neighborhood-Metric-Space :
    (x y : type-Metric-Space) (d₁ d₂ : ℚ⁺) →
    leq-ℚ⁺ d₁ d₂ →
    neighborhood-Metric-Space d₁ x y →
    neighborhood-Metric-Space d₂ x y
  weakly-monotonic-neighborhood-Metric-Space
    x y d₁⁺@(d₁ , _) d₂⁺@(d₂ , _) d₁≤d₂ Nd₁xy =
    trichotomy-le-ℚ d₁ d₂
      ( λ d₁<d₂ → monotonic-neighborhood-Metric-Space x y d₁⁺ d₂⁺ d₁<d₂ Nd₁xy)
      ( λ d₁=d₂ →
        tr (λ d → neighborhood-Metric-Space d x y) (eq-ℚ⁺ d₁=d₂) Nd₁xy)
      ( λ d₂<d₁ → ex-falso (not-leq-le-ℚ d₂ d₁ d₂<d₁ d₁≤d₂))

  saturated-neighborhood-Metric-Space :
    (ε : ℚ⁺) (x y : type-Metric-Space) →
    ((δ : ℚ⁺) → neighborhood-Metric-Space (ε +ℚ⁺ δ) x y) →
    neighborhood-Metric-Space ε x y
  saturated-neighborhood-Metric-Space =
    saturated-neighborhood-Pseudometric-Space pseudometric-Metric-Space
```

### Similarity of elements in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  sim-prop-Metric-Space : Relation-Prop l2 (type-Metric-Space A)
  sim-prop-Metric-Space =
    sim-prop-Pseudometric-Space (pseudometric-Metric-Space A)

  sim-Metric-Space : Relation l2 (type-Metric-Space A)
  sim-Metric-Space =
    sim-Pseudometric-Space (pseudometric-Metric-Space A)

  is-prop-sim-Metric-Space :
    (x y : type-Metric-Space A) →
    is-prop (sim-Metric-Space x y)
  is-prop-sim-Metric-Space =
    is-prop-sim-Pseudometric-Space (pseudometric-Metric-Space A)

  refl-sim-Metric-Space :
    (x : type-Metric-Space A) →
    sim-Metric-Space x x
  refl-sim-Metric-Space =
    refl-sim-Pseudometric-Space (pseudometric-Metric-Space A)

  sim-eq-Metric-Space :
    (x y : type-Metric-Space A) →
    x ＝ y →
    sim-Metric-Space x y
  sim-eq-Metric-Space =
    sim-eq-Pseudometric-Space (pseudometric-Metric-Space A)

  symmetric-sim-Metric-Space :
    (x y : type-Metric-Space A) →
    sim-Metric-Space x y →
    sim-Metric-Space y x
  symmetric-sim-Metric-Space =
    symmetric-sim-Pseudometric-Space (pseudometric-Metric-Space A)

  inv-sim-Metric-Space :
    {x y : type-Metric-Space A} →
    sim-Metric-Space x y →
    sim-Metric-Space y x
  inv-sim-Metric-Space {x} {y} =
    inv-sim-Pseudometric-Space (pseudometric-Metric-Space A)

  transitive-sim-Metric-Space :
    (x y z : type-Metric-Space A) →
    sim-Metric-Space y z →
    sim-Metric-Space x y →
    sim-Metric-Space x z
  transitive-sim-Metric-Space =
    transitive-sim-Pseudometric-Space (pseudometric-Metric-Space A)

  equivalence-sim-Metric-Space :
    equivalence-relation l2 (type-Metric-Space A)
  equivalence-sim-Metric-Space =
    equivalence-sim-Pseudometric-Space (pseudometric-Metric-Space A)
```

## Properties

### The carrier type of a metric space is a set

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-set-type-Metric-Space : is-set (type-Metric-Space A)
  is-set-type-Metric-Space =
    is-set-type-is-extensional-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( is-extensional-pseudometric-Metric-Space A)

  set-Metric-Space : Set l1
  set-Metric-Space =
    (type-Metric-Space A , is-set-type-Metric-Space)
```

### Similarity of elements in a metric space is equivalent to equality

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  equiv-sim-eq-Metric-Space :
    (x y : type-Metric-Space A) →
    (x ＝ y) ≃ sim-Metric-Space A x y
  equiv-sim-eq-Metric-Space =
    equiv-sim-eq-is-extensional-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( is-extensional-pseudometric-Metric-Space A)

  eq-sim-Metric-Space :
    (x y : type-Metric-Space A) →
    sim-Metric-Space A x y →
    x ＝ y
  eq-sim-Metric-Space x y =
    map-inv-equiv (equiv-sim-eq-Metric-Space x y)
```

### Characterization of the transport of metric structures along equalities

```agda
equiv-Eq-tr-Metric-Structure :
  {l1 l2 : Level} (A B : UU l1) →
  (P : Metric-Structure l2 A) →
  (Q : Metric-Structure l2 B) →
  (e : A ＝ B) →
  (tr (Metric-Structure l2) e P ＝ Q) ≃
  (Eq-Rational-Neighborhood-Relation
    ( pr1 P)
    ( preimage-Rational-Neighborhood-Relation (map-eq e) (pr1 Q)))
equiv-Eq-tr-Metric-Structure A .A P Q refl =
  ( equiv-Eq-eq-Rational-Neighborhood-Relation (pr1 P) (pr1 Q)) ∘e
  ( extensionality-type-subtype'
    ( is-metric-prop-Rational-Neighborhood-Relation A)
    ( P)
    ( Q))
```

## External links

- [`MetricSpaces.Type`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MetricSpaces.Type.html)
  at TypeTopology
- [metric space](https://ncatlab.org/nlab/show/metric+space) at $n$Lab
- [Metric spaces](https://en.wikipedia.org/wiki/Metric_space) at Wikipedia
