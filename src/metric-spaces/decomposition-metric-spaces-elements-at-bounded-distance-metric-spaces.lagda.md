# Decomposition of metric spaces as indexed sums of metric spaces with elements at bounded distance

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
{{#concept "Σ-decomposition into subspaces of elements at bounded distance" Agda=Σ-components-at-bounded-distance-Metric-Space}},
the [indexed sum](metric-spaces.indexed-sums-metric-spaces.md) of its
[subspaces](metric-spaces.subspaces-metric-spaces.md) of
[elements at bounded distance](metric-spaces.elements-at-bounded-distance-metric-spaces.md)
indexed by the [set quotient](foundation.set-quotients.md) of the metric space
by the [equivalence relation](foundation.equivalence-relations.md) of being at
bounded distance.

## Definitions

### The set of components of subspaces of elements at bounded distance in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  set-components-at-bounded-distance-Metric-Space : Set (l1 ⊔ l2)
  set-components-at-bounded-distance-Metric-Space =
    quotient-Set
      ( equivalence-relation-bounded-dist-Metric-Space A)

  type-components-at-bounded-distance-Metric-Space : UU (l1 ⊔ l2)
  type-components-at-bounded-distance-Metric-Space =
    type-Set set-components-at-bounded-distance-Metric-Space

  map-type-components-at-bounded-distance-Metric-Space :
    type-Metric-Space A →
    type-components-at-bounded-distance-Metric-Space
  map-type-components-at-bounded-distance-Metric-Space =
    quotient-map
      ( equivalence-relation-bounded-dist-Metric-Space A)
```

### The family of metric subspaces of elements at bounded distance

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (x : type-components-at-bounded-distance-Metric-Space A)
  where

  subspace-components-at-bounded-distance-Metric-Space :
    Metric-Space (l1 ⊔ l2) l2
  subspace-components-at-bounded-distance-Metric-Space =
    subspace-Metric-Space
      ( A)
      ( subtype-set-quotient
        ( equivalence-relation-bounded-dist-Metric-Space A)
        ( x))

  type-subspace-components-at-bounded-distance-Metric-Space : UU (l1 ⊔ l2)
  type-subspace-components-at-bounded-distance-Metric-Space =
    type-Metric-Space
      subspace-components-at-bounded-distance-Metric-Space
```

### The total metric space of bounded distance components

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  Σ-components-at-bounded-distance-Metric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  Σ-components-at-bounded-distance-Metric-Space =
    indexed-sum-Metric-Space
      ( set-components-at-bounded-distance-Metric-Space A)
      ( subspace-components-at-bounded-distance-Metric-Space A)

  type-Σ-components-at-bounded-distance-Metric-Space : UU (l1 ⊔ l2)
  type-Σ-components-at-bounded-distance-Metric-Space =
    type-Metric-Space Σ-components-at-bounded-distance-Metric-Space
```

## Properties

### All elements in a subspace of elements at bounded distance are at bounded distance

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (X : type-components-at-bounded-distance-Metric-Space A)
  where

  all-elements-at-bounded-distance-subspace-components-at-bounded-distance-Metric-Space :
    (x y : type-subspace-components-at-bounded-distance-Metric-Space A X) →
    bounded-dist-Metric-Space
      ( subspace-components-at-bounded-distance-Metric-Space A X)
      ( x)
      ( y)
  all-elements-at-bounded-distance-subspace-components-at-bounded-distance-Metric-Space
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

  lemma-iff-neighborhood-Σ-components-at-bounded-distance-Metric-Space :
    ( d : ℚ⁺) →
    ( X Y : type-components-at-bounded-distance-Metric-Space A) →
    ( eqXY : X ＝ Y) →
    ( x : type-subspace-components-at-bounded-distance-Metric-Space A X) →
    ( y : type-subspace-components-at-bounded-distance-Metric-Space A Y) →
    ( neighborhood-Metric-Space
      ( subspace-components-at-bounded-distance-Metric-Space A Y)
      ( d)
      ( tr
        ( type-Metric-Space ∘
          subspace-components-at-bounded-distance-Metric-Space A)
        ( eqXY)
        ( x))
      ( y)) ↔
    neighborhood-Metric-Space A d (pr1 x) (pr1 y)
  lemma-iff-neighborhood-Σ-components-at-bounded-distance-Metric-Space
    d X .X refl (x , x∈X) (y , y∈X) = id-iff
```

### Any metric space is isometrically equivalent to the indexed sum of its subspaces of components of elements at bounded distance

#### Equivalence of underlying types

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  equiv-type-Σ-components-at-bounded-distance-Metric-Space :
    type-Σ-components-at-bounded-distance-Metric-Space A ≃
    type-Metric-Space A
  equiv-type-Σ-components-at-bounded-distance-Metric-Space =
    Σ-decomposition-is-in-equivalence-class-set-quotient
      ( equivalence-relation-bounded-dist-Metric-Space A)

  map-equiv-Σ-components-at-bounded-distance-Metric-Space :
    type-function-Metric-Space
      ( Σ-components-at-bounded-distance-Metric-Space A)
      ( A)
  map-equiv-Σ-components-at-bounded-distance-Metric-Space =
    map-equiv
      ( equiv-type-Σ-components-at-bounded-distance-Metric-Space)
```

#### The equivalence between a metric space and its decompositions into subspaces of elements at bounded distance is an isometry

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  preserves-neighborhood-map-equiv-Σ-components-at-bounded-distance-Metric-Space :
    ( d : ℚ⁺)
    ( x y : type-Σ-components-at-bounded-distance-Metric-Space A) →
    neighborhood-Metric-Space
      ( Σ-components-at-bounded-distance-Metric-Space A)
      ( d)
      ( x)
      ( y) →
    neighborhood-Metric-Space A d
      ( map-equiv-Σ-components-at-bounded-distance-Metric-Space A x)
      ( map-equiv-Σ-components-at-bounded-distance-Metric-Space A y)
  preserves-neighborhood-map-equiv-Σ-components-at-bounded-distance-Metric-Space
    d (X , x , x∈X) (Y , y , y∈Y) (X=Y , Nxy) =
    forward-implication
      ( lemma-iff-neighborhood-Σ-components-at-bounded-distance-Metric-Space
        ( A)
        ( d)
        ( X)
        ( Y)
        ( X=Y)
        ( x , x∈X)
        ( y , y∈Y))
      ( Nxy)

  reflects-neighborhood-map-equiv-Σ-components-at-bounded-distance-Metric-Space :
    ( d : ℚ⁺)
    ( x y : type-Σ-components-at-bounded-distance-Metric-Space A) →
    neighborhood-Metric-Space A d
      ( map-equiv-Σ-components-at-bounded-distance-Metric-Space A x)
      ( map-equiv-Σ-components-at-bounded-distance-Metric-Space A y) →
    neighborhood-Metric-Space
      ( Σ-components-at-bounded-distance-Metric-Space A)
      ( d)
      ( x)
      ( y)
  reflects-neighborhood-map-equiv-Σ-components-at-bounded-distance-Metric-Space
    d (X , x , x∈X) (Y , y , y∈Y) Nxy =
    ( lemma-eq ,
      backward-implication
        ( lemma-iff-neighborhood-Σ-components-at-bounded-distance-Metric-Space
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
        map-type-components-at-bounded-distance-Metric-Space A y ＝ Y
      lemma-eq-Y =
        eq-set-quotient-equivalence-class-set-quotient
          ( equivalence-relation-bounded-dist-Metric-Space A)
          ( Y)
          ( y∈Y)

      lemma-eq-X :
        map-type-components-at-bounded-distance-Metric-Space A x ＝ X
      lemma-eq-X =
        eq-set-quotient-equivalence-class-set-quotient
          ( equivalence-relation-bounded-dist-Metric-Space A)
          ( X)
          ( x∈X)

      lemma-eq-map-type-components-at-bounded-distance-Metric-Space :
        ( map-type-components-at-bounded-distance-Metric-Space A x) ＝
        ( map-type-components-at-bounded-distance-Metric-Space A y)
      lemma-eq-map-type-components-at-bounded-distance-Metric-Space =
        apply-effectiveness-quotient-map'
          ( equivalence-relation-bounded-dist-Metric-Space A)
          ( unit-trunc-Prop (d , Nxy))

      lemma-eq : X ＝ Y
      lemma-eq =
        ( inv lemma-eq-X) ∙
        ( lemma-eq-map-type-components-at-bounded-distance-Metric-Space) ∙
        ( lemma-eq-Y)

  is-isometry-map-equiv-Σ-components-at-bounded-distance-Metric-Space :
    is-isometry-Metric-Space
      ( Σ-components-at-bounded-distance-Metric-Space A)
      ( A)
      ( map-equiv-Σ-components-at-bounded-distance-Metric-Space A)
  is-isometry-map-equiv-Σ-components-at-bounded-distance-Metric-Space d x y =
    ( ( preserves-neighborhood-map-equiv-Σ-components-at-bounded-distance-Metric-Space
        ( d)
        ( x)
        ( y)) ,
      ( reflects-neighborhood-map-equiv-Σ-components-at-bounded-distance-Metric-Space
        ( d)
        ( x)
        ( y)))
```

#### The isometric equivalence between a metric space and its decompositions into subspaces of elements at bounded distance

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  isometric-equiv-Σ-components-at-bounded-distance-Metric-Space :
    isometric-equiv-Metric-Space
      ( Σ-components-at-bounded-distance-Metric-Space A)
      ( A)
  isometric-equiv-Σ-components-at-bounded-distance-Metric-Space =
    ( equiv-type-Σ-components-at-bounded-distance-Metric-Space A ,
      is-isometry-map-equiv-Σ-components-at-bounded-distance-Metric-Space A)
```

### The decomposition into subspaces of elements at bounded distance is idempotent

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  idempotent-Σ-components-at-bounded-distance-Metric-Space :
    Σ-components-at-bounded-distance-Metric-Space
      ( Σ-components-at-bounded-distance-Metric-Space A) ＝
    Σ-components-at-bounded-distance-Metric-Space A
  idempotent-Σ-components-at-bounded-distance-Metric-Space =
    eq-isometric-equiv-Metric-Space
      ( Σ-components-at-bounded-distance-Metric-Space
        ( Σ-components-at-bounded-distance-Metric-Space A))
      ( Σ-components-at-bounded-distance-Metric-Space A)
      ( isometric-equiv-Σ-components-at-bounded-distance-Metric-Space
        ( Σ-components-at-bounded-distance-Metric-Space A))
```

