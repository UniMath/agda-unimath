# The bounded distance decomposition of metric spaces

```agda
module metric-spaces.decomposition-metric-spaces-elements-at-bounded-distance-metric-spaces where
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
{{#concept "bounded distance decomposition" Agda=total-bounded-distance-components-Metric-Space}},
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

  set-bounded-distance-components-Metric-Space : Set (l1 ⊔ l2)
  set-bounded-distance-components-Metric-Space =
    quotient-Set
      ( equivalence-relation-bounded-dist-Metric-Space A)

  type-bounded-distance-components-Metric-Space : UU (l1 ⊔ l2)
  type-bounded-distance-components-Metric-Space =
    type-Set set-bounded-distance-components-Metric-Space

  map-type-bounded-distance-components-Metric-Space :
    type-Metric-Space A →
    type-bounded-distance-components-Metric-Space
  map-type-bounded-distance-components-Metric-Space =
    quotient-map
      ( equivalence-relation-bounded-dist-Metric-Space A)
```

### The family of metric subspaces of elements at bounded distance

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (x : type-bounded-distance-components-Metric-Space A)
  where

  subspace-bounded-distance-components-Metric-Space :
    Metric-Space (l1 ⊔ l2) l2
  subspace-bounded-distance-components-Metric-Space =
    subspace-Metric-Space
      ( A)
      ( subtype-set-quotient
        ( equivalence-relation-bounded-dist-Metric-Space A)
        ( x))

  type-subspace-bounded-distance-components-Metric-Space : UU (l1 ⊔ l2)
  type-subspace-bounded-distance-components-Metric-Space =
    type-Metric-Space
      subspace-bounded-distance-components-Metric-Space
```

### The total metric space of bounded distance components

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  total-sum-bounded-distance-components-Metric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  total-sum-bounded-distance-components-Metric-Space =
    indexed-sum-Metric-Space
      ( set-bounded-distance-components-Metric-Space A)
      ( subspace-bounded-distance-components-Metric-Space A)

  type-total-sum-bounded-distance-components-Metric-Space : UU (l1 ⊔ l2)
  type-total-sum-bounded-distance-components-Metric-Space =
    type-Metric-Space total-sum-bounded-distance-components-Metric-Space
```

## Properties

### All elements of a bounded distance subspace are at bounded distance

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (X : type-bounded-distance-components-Metric-Space A)
  where

  all-elements-at-bounded-distance-subspace-bounded-distance-components-Metric-Space :
    (x y : type-subspace-bounded-distance-components-Metric-Space A X) →
    bounded-dist-Metric-Space
      ( subspace-bounded-distance-components-Metric-Space A X)
      ( x)
      ( y)
  all-elements-at-bounded-distance-subspace-bounded-distance-components-Metric-Space
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

  lemma-iff-neighborhood-total-sum-bounded-distance-components-Metric-Space :
    ( d : ℚ⁺) →
    ( X Y : type-bounded-distance-components-Metric-Space A) →
    ( eqXY : X ＝ Y) →
    ( x : type-subspace-bounded-distance-components-Metric-Space A X) →
    ( y : type-subspace-bounded-distance-components-Metric-Space A Y) →
    ( neighborhood-Metric-Space
      ( subspace-bounded-distance-components-Metric-Space A Y)
      ( d)
      ( tr
        ( type-Metric-Space ∘
          subspace-bounded-distance-components-Metric-Space A)
        ( eqXY)
        ( x))
      ( y)) ↔
    neighborhood-Metric-Space A d (pr1 x) (pr1 y)
  lemma-iff-neighborhood-total-sum-bounded-distance-components-Metric-Space
    d X .X refl (x , x∈X) (y , y∈X) = id-iff
```

### Metric spaces are isometrically equivalent to their bounded distance decomposition

#### Equivalence of underlying types

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  equiv-type-total-sum-bounded-distance-components-Metric-Space :
    type-total-sum-bounded-distance-components-Metric-Space A ≃
    type-Metric-Space A
  equiv-type-total-sum-bounded-distance-components-Metric-Space =
    Σ-decomposition-is-in-equivalence-class-set-quotient
      ( equivalence-relation-bounded-dist-Metric-Space A)

  map-equiv-total-sum-bounded-distance-components-Metric-Space :
    type-function-Metric-Space
      ( total-sum-bounded-distance-components-Metric-Space A)
      ( A)
  map-equiv-total-sum-bounded-distance-components-Metric-Space =
    map-equiv
      ( equiv-type-total-sum-bounded-distance-components-Metric-Space)
```

#### The equivalence between a metric space and its bounded distance decomposition is an isometry

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  preserves-neighborhood-map-equiv-total-sum-bounded-distance-components-Metric-Space :
    ( d : ℚ⁺)
    ( x y : type-total-sum-bounded-distance-components-Metric-Space A) →
    neighborhood-Metric-Space
      ( total-sum-bounded-distance-components-Metric-Space A)
      ( d)
      ( x)
      ( y) →
    neighborhood-Metric-Space A d
      ( map-equiv-total-sum-bounded-distance-components-Metric-Space A x)
      ( map-equiv-total-sum-bounded-distance-components-Metric-Space A y)
  preserves-neighborhood-map-equiv-total-sum-bounded-distance-components-Metric-Space
    d (X , x , x∈X) (Y , y , y∈Y) (X=Y , Nxy) =
    forward-implication
      ( lemma-iff-neighborhood-total-sum-bounded-distance-components-Metric-Space
        ( A)
        ( d)
        ( X)
        ( Y)
        ( X=Y)
        ( x , x∈X)
        ( y , y∈Y))
      ( Nxy)

  reflects-neighborhood-map-equiv-total-sum-bounded-distance-components-Metric-Space :
    ( d : ℚ⁺)
    ( x y : type-total-sum-bounded-distance-components-Metric-Space A) →
    neighborhood-Metric-Space A d
      ( map-equiv-total-sum-bounded-distance-components-Metric-Space A x)
      ( map-equiv-total-sum-bounded-distance-components-Metric-Space A y) →
    neighborhood-Metric-Space
      ( total-sum-bounded-distance-components-Metric-Space A)
      ( d)
      ( x)
      ( y)
  reflects-neighborhood-map-equiv-total-sum-bounded-distance-components-Metric-Space
    d (X , x , x∈X) (Y , y , y∈Y) Nxy =
    ( lemma-eq ,
      backward-implication
        ( lemma-iff-neighborhood-total-sum-bounded-distance-components-Metric-Space
          ( A)
          ( d)
          ( X)
          ( Y)
          ( lemma-eq)
          ( x , x∈X)
          ( y , y∈Y))
        ( Nxy))
    where

      lemma-eq-Y :
        map-type-bounded-distance-components-Metric-Space A y ＝ Y
      lemma-eq-Y =
        eq-set-quotient-equivalence-class-set-quotient
          ( equivalence-relation-bounded-dist-Metric-Space A)
          ( Y)
          ( y∈Y)

      lemma-eq-X :
        map-type-bounded-distance-components-Metric-Space A x ＝ X
      lemma-eq-X =
        eq-set-quotient-equivalence-class-set-quotient
          ( equivalence-relation-bounded-dist-Metric-Space A)
          ( X)
          ( x∈X)

      lemma-eq-map-type-bounded-distance-components-Metric-Space :
        ( map-type-bounded-distance-components-Metric-Space A x) ＝
        ( map-type-bounded-distance-components-Metric-Space A y)
      lemma-eq-map-type-bounded-distance-components-Metric-Space =
        apply-effectiveness-quotient-map'
          ( equivalence-relation-bounded-dist-Metric-Space A)
          ( unit-trunc-Prop (d , Nxy))

      lemma-eq : X ＝ Y
      lemma-eq =
        ( inv lemma-eq-X) ∙
        ( lemma-eq-map-type-bounded-distance-components-Metric-Space) ∙
        ( lemma-eq-Y)

  is-isometry-map-equiv-total-sum-bounded-distance-components-Metric-Space :
    is-isometry-Metric-Space
      ( total-sum-bounded-distance-components-Metric-Space A)
      ( A)
      ( map-equiv-total-sum-bounded-distance-components-Metric-Space A)
  is-isometry-map-equiv-total-sum-bounded-distance-components-Metric-Space
    d x y =
    ( ( preserves-neighborhood-map-equiv-total-sum-bounded-distance-components-Metric-Space
        ( d)
        ( x)
        ( y)) ,
      ( reflects-neighborhood-map-equiv-total-sum-bounded-distance-components-Metric-Space
        ( d)
        ( x)
        ( y)))
```

#### The isometric equivalence between a metric space and its bounded distance decomposition

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  isometric-equiv-total-sum-bounded-distance-components-Metric-Space :
    isometric-equiv-Metric-Space
      ( total-sum-bounded-distance-components-Metric-Space A)
      ( A)
  isometric-equiv-total-sum-bounded-distance-components-Metric-Space =
    ( equiv-type-total-sum-bounded-distance-components-Metric-Space A ,
      is-isometry-map-equiv-total-sum-bounded-distance-components-Metric-Space
        ( A))
```

### The bounded distance decomposition operation is idempotent

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  idempotent-total-sum-bounded-distance-components-Metric-Space :
    total-sum-bounded-distance-components-Metric-Space
      ( total-sum-bounded-distance-components-Metric-Space A) ＝
    total-sum-bounded-distance-components-Metric-Space A
  idempotent-total-sum-bounded-distance-components-Metric-Space =
    eq-isometric-equiv-Metric-Space
      ( total-sum-bounded-distance-components-Metric-Space
        ( total-sum-bounded-distance-components-Metric-Space A))
      ( total-sum-bounded-distance-components-Metric-Space A)
      ( isometric-equiv-total-sum-bounded-distance-components-Metric-Space
        ( total-sum-bounded-distance-components-Metric-Space A))
```
