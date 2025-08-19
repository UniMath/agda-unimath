# The bounded distance decomposition of metric spaces

```agda
module metric-spaces.bounded-distance-decompositions-of-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.elements-at-bounded-distance-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.indexed-sums-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

Any [metric space](metric-spaces.metric-spaces.md) is
[isometrically equivalent](metric-spaces.equality-of-metric-spaces.md) to its
{{#concept "bounded distance decomposition" Agda=bounded-distance-decomposition-Metric-Space}},
the [indexed sum](metric-spaces.indexed-sums-metric-spaces.md) of its
[subspaces](metric-spaces.subspaces-metric-spaces.md) of
[elements at bounded distance](metric-spaces.elements-at-bounded-distance-metric-spaces.md)
indexed by the [set quotient](foundation.set-quotients.md) of the metric space
by the [equivalence relation](foundation.equivalence-relations.md) of being at
bounded distance.

## Definitions

### The set of bounded distance components of a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  set-bounded-distance-component-Metric-Space : Set (l1 ⊔ l2)
  set-bounded-distance-component-Metric-Space =
    quotient-Set
      ( equivalence-relation-bounded-dist-Metric-Space A)

  type-bounded-distance-component-Metric-Space : UU (l1 ⊔ l2)
  type-bounded-distance-component-Metric-Space =
    type-Set set-bounded-distance-component-Metric-Space

  map-type-bounded-distance-component-Metric-Space :
    type-Metric-Space A →
    type-bounded-distance-component-Metric-Space
  map-type-bounded-distance-component-Metric-Space =
    quotient-map
      ( equivalence-relation-bounded-dist-Metric-Space A)
```

### The family of metric subspaces of elements at bounded distance

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (x : type-bounded-distance-component-Metric-Space A)
  where

  subspace-bounded-distance-component-Metric-Space :
    Metric-Space (l1 ⊔ l2) l2
  subspace-bounded-distance-component-Metric-Space =
    subspace-Metric-Space
      ( A)
      ( subtype-set-quotient
        ( equivalence-relation-bounded-dist-Metric-Space A)
        ( x))

  type-subspace-bounded-distance-component-Metric-Space : UU (l1 ⊔ l2)
  type-subspace-bounded-distance-component-Metric-Space =
    type-Metric-Space
      subspace-bounded-distance-component-Metric-Space
```

### The bounded distance decomposition of a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  bounded-distance-decomposition-Metric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  bounded-distance-decomposition-Metric-Space =
    indexed-sum-Metric-Space
      ( set-bounded-distance-component-Metric-Space A)
      ( subspace-bounded-distance-component-Metric-Space A)

  type-bounded-distance-decomposition-Metric-Space : UU (l1 ⊔ l2)
  type-bounded-distance-decomposition-Metric-Space =
    type-Metric-Space bounded-distance-decomposition-Metric-Space
```

## Properties

### All elements of a bounded distance subspace are at bounded distance

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (X : type-bounded-distance-component-Metric-Space A)
  where

  all-elements-at-bounded-distance-subspace-bounded-distance-component-Metric-Space :
    (x y : type-subspace-bounded-distance-component-Metric-Space A X) →
    bounded-dist-Metric-Space
      ( subspace-bounded-distance-component-Metric-Space A X)
      ( x)
      ( y)
  all-elements-at-bounded-distance-subspace-bounded-distance-component-Metric-Space
    (x , x∈X) (y , y∈X) =
    apply-effectiveness-quotient-map
      ( equivalence-relation-bounded-dist-Metric-Space A)
      ( ( eq-set-quotient-equivalence-class-set-quotient
          ( equivalence-relation-bounded-dist-Metric-Space A)
          ( X)
          ( x∈X)) ∙
        ( inv
          ( eq-set-quotient-equivalence-class-set-quotient
            ( equivalence-relation-bounded-dist-Metric-Space A)
            ( X)
            ( y∈X))))
```

### Neighborhoods in subspaces of equal components are neigborhoods in the ambient metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  lemma-iff-neighborhood-bounded-distance-decomposition-Metric-Space :
    ( d : ℚ⁺) →
    ( X Y : type-bounded-distance-component-Metric-Space A) →
    ( eqXY : X ＝ Y) →
    ( x : type-subspace-bounded-distance-component-Metric-Space A X) →
    ( y : type-subspace-bounded-distance-component-Metric-Space A Y) →
    ( neighborhood-Metric-Space
      ( subspace-bounded-distance-component-Metric-Space A Y)
      ( d)
      ( tr
        ( type-Metric-Space ∘
          subspace-bounded-distance-component-Metric-Space A)
        ( eqXY)
        ( x))
      ( y)) ↔
    neighborhood-Metric-Space A d (pr1 x) (pr1 y)
  lemma-iff-neighborhood-bounded-distance-decomposition-Metric-Space
    d X .X refl (x , x∈X) (y , y∈X) = id-iff
```

### Metric spaces are isometrically equivalent to their bounded distance decomposition

#### Equivalence of underlying types

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  equiv-type-bounded-distance-decomposition-Metric-Space :
    type-bounded-distance-decomposition-Metric-Space A ≃
    type-Metric-Space A
  equiv-type-bounded-distance-decomposition-Metric-Space =
    Σ-decomposition-is-in-equivalence-class-set-quotient
      ( equivalence-relation-bounded-dist-Metric-Space A)

  map-equiv-bounded-distance-decomposition-Metric-Space :
    type-function-Metric-Space
      ( bounded-distance-decomposition-Metric-Space A)
      ( A)
  map-equiv-bounded-distance-decomposition-Metric-Space =
    map-equiv
      ( equiv-type-bounded-distance-decomposition-Metric-Space)
```

#### The equivalence between a metric space and its bounded distance decomposition is an isometry

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  preserves-neighborhood-map-equiv-bounded-distance-decomposition-Metric-Space :
    ( d : ℚ⁺)
    ( x y : type-bounded-distance-decomposition-Metric-Space A) →
    neighborhood-Metric-Space
      ( bounded-distance-decomposition-Metric-Space A)
      ( d)
      ( x)
      ( y) →
    neighborhood-Metric-Space A d
      ( map-equiv-bounded-distance-decomposition-Metric-Space A x)
      ( map-equiv-bounded-distance-decomposition-Metric-Space A y)
  preserves-neighborhood-map-equiv-bounded-distance-decomposition-Metric-Space
    d (X , x , x∈X) (Y , y , y∈Y) (X=Y , Nxy) =
    forward-implication
      ( lemma-iff-neighborhood-bounded-distance-decomposition-Metric-Space
        ( A)
        ( d)
        ( X)
        ( Y)
        ( X=Y)
        ( x , x∈X)
        ( y , y∈Y))
      ( Nxy)

  reflects-neighborhood-map-equiv-bounded-distance-decomposition-Metric-Space :
    ( d : ℚ⁺)
    ( x y : type-bounded-distance-decomposition-Metric-Space A) →
    neighborhood-Metric-Space A d
      ( map-equiv-bounded-distance-decomposition-Metric-Space A x)
      ( map-equiv-bounded-distance-decomposition-Metric-Space A y) →
    neighborhood-Metric-Space
      ( bounded-distance-decomposition-Metric-Space A)
      ( d)
      ( x)
      ( y)
  reflects-neighborhood-map-equiv-bounded-distance-decomposition-Metric-Space
    d (X , x , x∈X) (Y , y , y∈Y) Nxy =
    ( lemma-eq ,
      backward-implication
        ( lemma-iff-neighborhood-bounded-distance-decomposition-Metric-Space
          ( A)
          ( d)
          ( X)
          ( Y)
          ( lemma-eq)
          ( x , x∈X)
          ( y , y∈Y))
        ( Nxy))
    where

    lemma-eq : X ＝ Y
    lemma-eq =
      eq-set-quotient-sim-element-set-quotient
        ( equivalence-relation-bounded-dist-Metric-Space A)
        ( X)
        ( Y)
        ( x∈X)
        ( y∈Y)
        ( unit-trunc-Prop (d , Nxy))

  is-isometry-map-equiv-bounded-distance-decomposition-Metric-Space :
    is-isometry-Metric-Space
      ( bounded-distance-decomposition-Metric-Space A)
      ( A)
      ( map-equiv-bounded-distance-decomposition-Metric-Space A)
  is-isometry-map-equiv-bounded-distance-decomposition-Metric-Space
    d x y =
    ( ( preserves-neighborhood-map-equiv-bounded-distance-decomposition-Metric-Space
        ( d)
        ( x)
        ( y)) ,
      ( reflects-neighborhood-map-equiv-bounded-distance-decomposition-Metric-Space
        ( d)
        ( x)
        ( y)))
```

#### The isometric equivalence between a metric space and its bounded distance decomposition

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  isometric-equiv-bounded-distance-decomposition-Metric-Space :
    isometric-equiv-Metric-Space
      ( bounded-distance-decomposition-Metric-Space A)
      ( A)
  isometric-equiv-bounded-distance-decomposition-Metric-Space =
    ( equiv-type-bounded-distance-decomposition-Metric-Space A ,
      is-isometry-map-equiv-bounded-distance-decomposition-Metric-Space A)
```

### The bounded distance decomposition operation is idempotent

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-idempotent-bounded-distance-decomposition-Metric-Space :
    bounded-distance-decomposition-Metric-Space
      ( bounded-distance-decomposition-Metric-Space A) ＝
    bounded-distance-decomposition-Metric-Space A
  is-idempotent-bounded-distance-decomposition-Metric-Space =
    eq-isometric-equiv-Metric-Space
      ( bounded-distance-decomposition-Metric-Space
        ( bounded-distance-decomposition-Metric-Space A))
      ( bounded-distance-decomposition-Metric-Space A)
      ( isometric-equiv-bounded-distance-decomposition-Metric-Space
        ( bounded-distance-decomposition-Metric-Space A))
```
